---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture-note
tags: literate
order: 20
shortTitle: "Barrier example"
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Specification and Proof of a Concurrent Barrier

> Follow these notes in Rocq at [src/sys_verif/notes/barrier.v](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/src/sys_verif/notes/barrier.v).

## Learning outcomes

1. Understand how more sophisticated resource algebras help.
2. Explain the barrier's specification in the language of separation logic.
3. Follow how the proof uses ghost state to construct the desired specification.

<!-- @include: ./macros.snippet.md -->

## Motivation

We've been looking at small examples so far. In this lecture, we'll get to see a non-trivial (and useful) synchronization primitive and a non-trivial specification designed for that code.

The subject of this lecture is a _barrier_. Barriers are part of a group of synchronization primitives, which are the tools used to coordinate threads in a concurrent program. The first and most core primitive is the lock, as we've seen with `sync.Mutex` several times. A lock guarantees mutual exclusion: only one thread can hold the lock at any given time. A barrier provides a very different function: it allows one thread to wait for potentially many other threads to complete.

## Warmup: Spawn/Join

Before getting to the barrier proof, it helps to see the implementation, specification, and proof of the `std.Spawn` and `Join()` API we used previously without looking at the details. We can see `Join()` as a restrictives barrier: it is only used to wait for a specific spawned thread, not a set of threads as the full barrier implementation will support.

We have to incidentally talk about another synchronization primitive, the condition variable, which Go provides as `sync.Cond`. A condition variable is a low-level primitive that allows one thread to signal to another; it is often used to build other synchronization primitives.

### Condition variables

A condition variable is operationally very simple; using it correctly is a bit tricky, though. Upon initialization, a condition variable is always associated with a mutex, hence `sync.NewCond(mu)` takes a mutex `mu` as an argument. The two key operations are `c.Broadcast()`, which wakes up all waiting threads, and `c.Wait()`, which unlocks the mutex, puts the current thread to sleep, and locks the mutex upon receiving a broadcast. As this indicates, a thread should always hold the mutex when it calls `c.Wait()`. (There is also `c.Signal()` which signals an arbitrary waiting thread rather than all of them.)

It is almost always the case that `c.Wait()` is called in a loop that checks some condition protected by the mutex, then calls `c.Wait()`, then re-checks it upon re-acquiring the lock (this is where the name "condition variable" comes from). The benefit of the condition variable is that rather than check the condition as fast as possible, the waiting thread can go to sleep and consume little resources, but we still arrange for another thread to wake it up when the condition becomes true.

The GooseLang model of `c.Wait()` is simply `c.mu.Unlock(); c.mu.Lock()`. This captures the possible scheduling behaviors but doesn't take into account signaling, which unblocks this call in between the unlock and lock. We use such a model because we aren't proving termination: in reality, that call to `c.mu.Lock()` would never happen if no other thread signals to the condition variable, but for proving partial correctness the GooseLang model is adequate (it turns some infinite loops into terminating ones). If we wanted to prove liveness, a more sophisticated model would be required.

### Implementing Spawn/Join

Here's the implementation of Spawn and Join from the Goose standard library:

```go
// JoinHandle is a mechanism to wait for a goroutine to finish. Calling `Join()`
// on the handle returned by `Spawn(f)` will wait for f to finish.
type JoinHandle struct {
	mu   *sync.Mutex
	done bool
	cond *sync.Cond
}

func newJoinHandle() *JoinHandle {
	mu := new(sync.Mutex)
	cond := sync.NewCond(mu)
	return &JoinHandle{
		mu:   mu,
		done: false,
		cond: cond,
	}
}

func (h *JoinHandle) finish() {
	h.mu.Lock()
	h.done = true
	h.cond.Signal()
	h.mu.Unlock()
}

// Spawn runs `f` in a parallel goroutine and returns a handle to wait for
// it to finish.
func Spawn(f func()) *JoinHandle {
	h := newJoinHandle()
	go func() {
		f()
		h.finish()
	}()
	return h
}

func (h *JoinHandle) Join() {
	h.mu.Lock()
	for {
		if h.done {
			// the proof is a bit easier if we do this; it will cause a second
			// Join() (which is a misuse of the API) to fail
			h.done = false
			break
		}
		h.cond.Wait()
	}
	h.mu.Unlock()
}
```

The main state tracked by a `JoinHandle` is a boolean `done` that tracks if the spawned thread has finished. `Join()` checks this condition in a loop, calling `h.cond.Wait()` in each iteration. In between iterations it calls `h.cond.Wait()`, which remember unlocks that mutex, sleeps until a signal, then re-locks the mutex.

**Exercise:** what would happen if we implemented `h.Join()` like this, imagining that `finish()` signals the condition variable so this is enough:

```go
h.mu.Lock()
h.cond.Wait()
h.mu.Unlock()
```

::: details Solution

This would lead to deadlock if `h.finish()` is called before `Join()`: the signal would come _first_ (and be lost), so the `Wait()` would never return. Unfortunately our verification won't help with this problem! We're only proving partial correctness and this is instead a liveness issue.

This problem is also why we need the `done` variable.

:::

### Specifying and verifying Spawn/Join

We already used the specification for this library in the first proof of the parallel add example. Recall that the basic idea was to promise something as the postcondition for the spawned thread, and then to return that assertion in `Join`. Here's what that looks like:

```rocq
Lemma wp_Spawn (Q: iProp Σ) (f: val) :
  {{{ WP f #() {{ Q }} }}}
    Spawn f
  {{{ (l: loc), RET #l; is_JoinHandle l Q }}}.

Lemma wp_JoinHandle__Join (l: loc) (Q: iProp Σ) :
  {{{ is_JoinHandle l Q }}}
    JoinHandle__Join #l
  {{{ RET #(); Q }}}
```

The proof of this specification boils down to a careful choice of the lock invariant for the mutex in a `JoinHandle`. The lock invariant used in the proof is `∃ (done_b: bool), l ↦s[JoinHandle :: "done"] done_b ∗ (if done_b then P else True)`. What makes this work is that in `Join()`, if we discover that the thread has finished, the code sets `done` back to false, so the proof can extract the `P` in the lock invariant and restore it with merely `True`.

The barrier specification builds on the core idea of Spawn and Join.

## Implementation

### Barrier, at a high-level

The desired API has four operations:

- `NewBarrier() *Barrier` creates a new barrier.
- `(b *Barrier) Add(n uint64)` increments the number of threads this barrier is waiting for by `n` (often 1). Typically performed by the same goroutine that created the barrier.
- `(b *Barrier) Done()` (typically called in a different goroutine) marks one of the waiting threads as done.
- `(b *Barrier) Wait()` blocks until all threads we're waiting for have called `Done()`.

It is possible to interleave `Add()` and `Done()` calls, so that the number of waiting threads goes up and down.

It is also possible for several threads to call `Wait()`, and all of those calls will return when the last spawned goroutine calls `Done()`. However, we will focus our specification in this lecture on the case where there's a single call to `Wait()`, as in the common pattern of spawning a number of background threads and then waiting for all of them (you might have written code like this in the shell using `&` to spawn background threads and `wait` to wait for all of them).

### Barrier code

Using condition variables, we can implement an efficient barrier.

```go
// A simple barrier, very similar to a Go `sync.WaitGroup`.

type Barrier struct {
	numWaiting uint64
	mu         *sync.Mutex
	cond       *sync.Cond
}

// Create a new barrier waiting for no threads.
func NewBarrier() *Barrier {
	mu := new(sync.Mutex)
	cond := sync.NewCond(mu)
	return &Barrier{numWaiting: 0, mu: mu, cond: cond}
}

// Add `n` threads that the barrier is waiting to call `Done()`.
func (b *Barrier) Add(n uint64) {
	b.mu.Lock()
	b.numWaiting = std.SumAssumeNoOverflow(b.numWaiting, n)
	b.mu.Unlock()
}

// Mark one thread as done.
func (b *Barrier) Done() {
	b.mu.Lock()
	if b.numWaiting == 0 {
		panic("Done() called too many times")
	}
	b.numWaiting = b.numWaiting - 1
	if b.numWaiting == 0 {
		b.cond.Broadcast()
	}
	b.mu.Unlock()
}

// Wait blocks until all threads pending with `Add()` have called `Done()`.
func (b *Barrier) Wait() {
	b.mu.Lock()
	for b.numWaiting > 0 {
		b.cond.Wait()
	}
	b.mu.Unlock()
}
```

The barrier essentially tracks a number of waiting threads `numWaiting` protected by a mutex. `Add` increments this count, `Done` decrements it. The main complication is that `Wait()` uses a condition variable to wait for `numWaiting` to become 0, and `Done()` is carefully written to broadcast to any `Wait()`ing threads.

Our barrier implementation works, but it's a bit simpler than the implementation of Go's `sync.WaitGroup` whose API we're copying. I encourage you to actually take a look at the `sync.WaitGroup` [source code](https://cs.opensource.google/go/go/+/refs/tags/go1.23.3:src/sync/waitgroup.go;l=25). The main bit of context you may need is that the references to `race` are about the Go race detector: most of this implementation is making the race detector correctly handle synchronization created by WaitGroup rather than the core functionality of the barrier.

Before getting to the specification and proof, let's see how we would use a barrier. The example we have returns to our favorite parallel add example. Note that in this version we are not using `std.Spawn`, replacing that with a barrier; we return to using a mutex and not using `AtomicInt`. This implementation is a bit more efficient, especially when waiting for a larger number of threads, since we wait for all threads simultaneously rather than each individually.

```go
func ParallelAdd2() uint64 {
	var x uint64 = 0
	m := new(sync.Mutex)
	b := NewBarrier()
	b.Add(1)
	b.Add(1)
	go func() {
		m.Lock()
		x = std.SumAssumeNoOverflow(x, 2)
		m.Unlock()
		b.Done()
	}()
	go func() {
		m.Lock()
		x = std.SumAssumeNoOverflow(x, 2)
		m.Unlock()
		b.Done()
	}()

	b.Wait()
	m.Lock()
	x_now := x
	m.Unlock()
	return x_now
}
```

## Specifying the barrier

This is the most interesting part of the proof: what does the barrier do? How do we express it in a way that will be useful to proofs of code that uses this synchronization primitive?

**Exercise:** write out a specification in terms of atomic operations for the barrier, in the style you saw in the previous lecture (which we call HOCAP). You'll have to invent something for `Wait()`.

Aside: the specification I settled on for the demo was inspired by Simcha van Collem's bachelor's thesis [Verifying a Barrier using Iris](https://www.cs.ru.nl/bachelors-theses/2023/Simcha_van_Collem___1040283___Verifying_a_Barrier_using_Iris.pdf) at Radboud University. We only need the "simple barrier" from that thesis, and I used the idea of send splitting but didn't implement receive splitting.

The barrier specification is based on three predicates:

- `is_barrier ℓ γ`
- `recv γ Q` says that calling `Wait()` will return the postcondition `Q` (because that's what all the threads we're waiting for will return)
- `send γ P` gives permission to call `Done()` once if a thread also proves `P`.

The `γ` is a ghost variable that ties the `recv` and `send` predicates to this barrier, which ensures that the assertions for different barriers are all distinct.

`is_barrier ℓ γ` is a persistent proposition, shared among threads, but `recv` and `send` are not duplicated.

The specifications of each operation are as follows. I've omitted `is_barrier ℓ γ` from preconditions to keep things cleaner as well as `γ`, but these are also needed.

- $\hoare{\True}{\mathrm{NewBarrier}()}{\fun{\ell} ∃ γ.\, \mathrm{is\_barrier}(\ell, γ)}$
- $\hoare{\mathrm{recv}(Q)}{\mathrm{Add}(1)}{\mathrm{recv}(Q ∗ P) ∗ \mathrm{send}(P)}$
- $\hoare{\mathrm{send}(P) ∗ P}{\mathrm{Done}()}{\True}$
- $\hoare{\mathrm{recv}(Q)}{\mathrm{Wait}()}{Q}$

The basic idea of using the specification is that we will create `recv γ (P1 ∗ P2 ∗ ... ∗ Pn)` and `send γ P1 ∗ send γ P2 ∗ ... ∗ send γ Pn` along the way while calling `Add(1)`. The `send` predicates create _separate_ obligations for each thread calling `Done`. We carefully account for all of these obligations: the predicate in `recv` is the conjunction of all `send`s. This ensures that when all threads finish and `Wait` returns we're able to return `Q` as a postcondition.

## Using the barrier spec

```rocq
From sys_verif.program_proof Require Import prelude empty_ffi.

From sys_verif.program_proof Require Import concurrent_init.
From sys_verif.program_proof Require Import demos.barrier_proof.

From Perennial.algebra Require Import ghost_var.

Open Scope Z_scope.

Section proof.
  Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.
  Context `{ghost_varG0: ghost_varG Σ Z}.
  Context `{barrierG0: barrier.barrierG Σ}.

  Definition lock_inv γ1 γ2 l : iProp _ :=
    ∃ (x: w64) (x1 x2: Z),
      "Hx1" :: ghost_var γ1 (DfracOwn (1/2)) x1 ∗
      "Hx2" :: ghost_var γ2 (DfracOwn (1/2)) x2 ∗
      "x" ∷ l ↦ x ∗
      "%Hsum" ∷ ⌜uint.Z x = (x1 + x2)%Z⌝.

  Lemma wp_ParallelAdd2 :
    {{{ is_pkg_init concurrent }}}
      @! concurrent.ParallelAdd2 #()
    {{{ (x: w64), RET #x; ⌜uint.Z x = 4⌝ }}}.
  Proof using All.
    wp_start as "_".
    iMod (ghost_var_alloc 0) as (γ1) "[Hv1_1 Hx1_2]".
    iMod (ghost_var_alloc 0) as (γ2) "[Hv2_1 Hx2_2]".
    wp_auto.
    wp_alloc mu_l as "Hmu".
    wp_auto.
    iMod (init_Mutex (lock_inv γ1 γ2 x_ptr) with "Hmu [$x $Hv1_1 $Hv2_1]") as "#Hlock".
    { iPureIntro. done. }
    wp_apply (barrier.wp_New).
    iIntros (l γ_b) "[#Hbar Hdone]". wp_auto.
    iPersist "m b".
    wp_apply (barrier.wp_Barrier__Add1 (ghost_var γ1 (DfracOwn (1/2)) 2) with "[$Hbar $Hdone]").
    iIntros "[Hsend1 Hdone]". wp_auto.
    wp_apply (barrier.wp_Barrier__Add1 (ghost_var γ2 (DfracOwn (1/2)) 2) with "[$Hbar $Hdone]").
    iIntros "[Hsend2 Hdone]". wp_auto.
    wp_bind (Fork _).
    iApply (wp_fork with "[Hx1_2 Hsend1]").
    { iModIntro.
      wp_auto.
      wp_apply (wp_Mutex__Lock with "[$Hlock]"). iIntros "[locked Hinv]". iNamed "Hinv".
      wp_auto.
      wp_apply (std.wp_SumAssumeNoOverflow). iIntros "%Hoverflow".
      wp_auto.
      iDestruct (ghost_var_agree with "Hx1_2 Hx1") as %Heq; subst.
      iMod (ghost_var_update_2 2 with "Hx1_2 Hx1") as "[Hx1_2 Hx1]".
      { rewrite dfrac_op_own Qp.half_half //. }
      wp_apply (wp_Mutex__Unlock with "[$Hlock $locked Hx1 Hx2 x]").
      { iFrame. iPureIntro.  word. }
      wp_apply (barrier.wp_Barrier__Done with "[$Hbar Hsend1 Hx1_2]").
      { iFrame "Hsend1". iFrame. }
      done.
    }

    iModIntro. wp_auto.
    wp_bind (Fork _).
    iApply (wp_fork with "[Hx2_2 Hsend2]").
    { iModIntro. wp_auto.
      wp_apply (wp_Mutex__Lock with "[$Hlock]"). iIntros "[locked Hinv]". iNamed "Hinv".
      wp_auto.
      wp_apply (std.wp_SumAssumeNoOverflow). iIntros "%Hoverflow".
      wp_auto.
      iDestruct (ghost_var_agree with "Hx2_2 Hx2") as %Heq; subst.
      iMod (ghost_var_update_2 2 with "Hx2_2 Hx2") as "[Hx2_2 Hx2]".
      { rewrite dfrac_op_own Qp.half_half //. }
      wp_apply (wp_Mutex__Unlock with "[$Hlock $locked Hx1 Hx2 x]").
      { iFrame. iPureIntro.  word. }
      wp_apply (barrier.wp_Barrier__Done with "[$Hbar $Hsend2 Hx2_2]").
      { iFrame. }
      done.
    }

    iModIntro.
    wp_auto.
    wp_apply (barrier.wp_Barrier__Wait with "[$Hbar $Hdone]").
    iIntros "[Hdone Hrecv]". iDestruct "Hdone" as "((_ & Hx1_2) & Hx2_2)".
    wp_auto.
    wp_apply (wp_Mutex__Lock with "[$Hlock]"). iIntros "[locked Hinv]". iNamed "Hinv".
    iDestruct (ghost_var_agree with "Hx1_2 Hx1") as %Heq; subst.
    iDestruct (ghost_var_agree with "Hx2_2 Hx2") as %Heq; subst.
    wp_auto.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $locked $x $Hx1 $Hx2]").
    { iPureIntro. word. }

    iApply "HΦ".
    iPureIntro.
    word.
  Qed.

End proof.

```

## Verifying the barrier

See the separate [barrier proof](./program-proofs/demos/barrier_proof.md) for how the proof works.

This proof uses an `auth_set` ghost state construction that is defined and verified in its own file, [auth set](./program-proofs/demos/auth_set.md).
