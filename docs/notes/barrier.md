---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture
tags: literate
order: 20
shortTitle: "Lecture 21: Barrier example"
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Lecture 21: Proof of a Concurrent Barrier

> Follow these notes in Coq at [src/sys_verif/program_proof/barrier.v](https://github.com/tchajed/sys-verif-fa24-proofs/blob/main/src/sys_verif/program_proof/barrier.v).

## Learning outcomes

1. Understand how more sophisticated resource algebras help.
2. Explain what a barrier does in the language of separation logic.

<!-- @include: ./macros.snippet.md -->

## Motivation

We've been looking at small examples so far. In this lecture, we'll get to see a non-trivial (and useful) synchronization primitive and a non-trivial specification designed for that code.

The subject of this lecture is a _barrier_. Barriers are part of a group of synchronization primitives, which are the tools used to coordinate threads in a concurrent program. The first and most core primitive is the lock, as we've seen with `sync.Mutex` several times. A lock guarantees mutual exclusion: only one thread can hold the lock at any given time. A barrier provides a very different function: it allows one thread to wait (for potentially many other threads).

## Implementation

### Condition variables

We have to incidentally talk about another synchronization primitive, the condition variable, which Go provides as `sync.Cond`. A condition variable is a low-level primitive that allows one thread to signal to another; it is often used to build other condition variables.

A condition variable is operationally very simple; using it correctly is a bit tricky, though. Upon initialization, a condition variable is always associated with a mutex, hence `sync.NewCond(mu)` takes a mutex `mu` as an argument. The two key operations are `c.Broadcast()`, which wakes up all waiting threads, and `c.Wait()`, which unlocks the mutex, puts the current thread to sleep, and locks the mutex upon receiving a broadcast. As this indicates, a thread should always hold the mutex when it calls `c.Wait()`. (There is also `c.Signal()` which signals an arbitrary waiting thread rather than all of them.)

It is almost always the case that `c.Wait()` is called in a loop that checks some condition protected by the mutex, then calls `c.Wait()`, then re-checks it upon re-acquiring the lock (this is where the name "condition variable" comes from). The benefit of the condition variable is that rather than check the condition as fast as possible, the waiting thread can go to sleep and consume little resources, but we still arrange for another thread to wake it up when the condition becomes true.

The GooseLang model of `c.Wait()` is simply `c.mu.Lock(); c.mu.Unlock()`. This captures the possible scheduling behaviors but doesn't take into account signaling. This is because we aren't proving termination: in reality, that call to `c.mu.Unlock()` would never happen if we fail to signal to the condition variable, but for proving partial correctness the GooseLang model is adequate (it turns some infinite loops into terminating ones).

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

Before getting to the proof, let's see how we would use a barrier. The example we have returns to our favorite parallel add example. Note that in this version we are not using `std.Spawn`, replacing that with a barrier; we return to using a mutex and not using `AtomicInt`. This implementation is a bit more efficient, especially when waiting for a larger number of threads, since we wait for all threads simultaneously rather than each individually.

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

## Using the barrier spec

```coq
From sys_verif.program_proof Require Import prelude empty_ffi.
From Perennial.program_proof Require Import std_proof.
From Perennial.algebra Require Import ghost_var.

From Goose.sys_verif_code Require Import concurrent.
From sys_verif.program_proof.concurrent Require Import barrier_proof.

Open Scope Z_scope.

Section proof.
  Context `{hG: !heapGS Σ}.
  Context `{ghost_varG0: ghost_varG Σ Z}.
  Context `{barrierG0: barrier.barrierG Σ}.

  Definition lock_inv γ1 γ2 l : iProp _ :=
    ∃ (x: w64) (x1 x2: Z),
      "Hx1" :: ghost_var γ1 (DfracOwn (1/2)) x1 ∗
      "Hx2" :: ghost_var γ2 (DfracOwn (1/2)) x2 ∗
      "x" ∷ l ↦[uint64T] #x ∗
      "%Hsum" ∷ ⌜uint.Z x = (x1 + x2)%Z⌝.

  Lemma wp_ParallelAdd2 :
    {{{ True }}}
      ParallelAdd2 #()
    {{{ (x: w64), RET #x; ⌜uint.Z x = 4⌝ }}}.
  Proof using All.
    wp_start as "_".
    iMod (ghost_var_alloc 0) as (γ1) "[Hv1_1 Hx1_2]".
    iMod (ghost_var_alloc 0) as (γ2) "[Hv2_1 Hx2_2]".
    wp_alloc x_l as "x".
    wp_apply (wp_newMutex nroot _ (lock_inv γ1 γ2 x_l) with "[$x $Hv1_1 $Hv2_1]").
    { iPureIntro. done. }
    iIntros (mu_l) "#Hlock".
    wp_pures.
    wp_apply (barrier.wp_NewBarrier). iIntros (l γ_b) "[#Hbar Hdone]".
    wp_apply (barrier.wp_Barrier__Add1 (ghost_var γ1 (DfracOwn (1/2)) 2) with "[$Hbar $Hdone]").
    iIntros "[Hsend1 Hdone]".
    wp_apply (barrier.wp_Barrier__Add1 (ghost_var γ2 (DfracOwn (1/2)) 2) with "[$Hbar $Hdone]").
    iIntros "[Hsend2 Hdone]".
    wp_apply (wp_fork with "[Hx1_2 Hsend1]").
    { iModIntro.
      wp_apply (wp_Mutex__Lock with "[$Hlock]"). iIntros "[locked Hinv]". iNamed "Hinv".
      wp_load.
      wp_apply (std_proof.wp_SumAssumeNoOverflow). iIntros "%Hoverflow".
      wp_store.
      iDestruct (ghost_var_agree with "Hx1_2 Hx1") as %Heq; subst.
      iMod (ghost_var_update_2 2 with "Hx1_2 Hx1") as "[Hx1_2 Hx1]".
      { rewrite dfrac_op_own Qp.half_half //. }
      wp_apply (wp_Mutex__Unlock with "[$Hlock $locked Hx1 Hx2 x]").
      { iFrame. iPureIntro.  word. }
      wp_apply (barrier.wp_Barrier__Done with "[$Hbar Hsend1 Hx1_2]").
      { iFrame "Hsend1". iFrame. }
      done.
    }

    wp_apply (wp_fork with "[Hx2_2 Hsend2]").
    { iModIntro.
      wp_apply (wp_Mutex__Lock with "[$Hlock]"). iIntros "[locked Hinv]". iNamed "Hinv".
      wp_load.
      wp_apply (std_proof.wp_SumAssumeNoOverflow). iIntros "%Hoverflow".
      wp_store.
      iDestruct (ghost_var_agree with "Hx2_2 Hx2") as %Heq; subst.
      iMod (ghost_var_update_2 2 with "Hx2_2 Hx2") as "[Hx2_2 Hx2]".
      { rewrite dfrac_op_own Qp.half_half //. }
      wp_apply (wp_Mutex__Unlock with "[$Hlock $locked Hx1 Hx2 x]").
      { iFrame. iPureIntro.  word. }
      wp_apply (barrier.wp_Barrier__Done with "[$Hbar $Hsend2 Hx2_2]").
      { iFrame. }
      done.
    }

    wp_apply (barrier.wp_Barrier__Wait with "[$Hbar $Hdone]").
    iIntros "[Hdone Hrecv]". iDestruct "Hdone" as "((_ & Hx1_2) & Hx2_2)".
    wp_apply (wp_Mutex__Lock with "[$Hlock]"). iIntros "[locked Hinv]". iNamed "Hinv".
    iDestruct (ghost_var_agree with "Hx1_2 Hx1") as %Heq; subst.
    iDestruct (ghost_var_agree with "Hx2_2 Hx2") as %Heq; subst.
    wp_load.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $locked $x $Hx1 $Hx2]").
    { iPureIntro. word. }

    wp_pures. iModIntro. iApply "HΦ".
    iPureIntro.
    word.
  Qed.

End proof.

```

## Verifying the barrier

See the separate [barrier proof](./program-proofs/barrier_proof.md).

This proof uses a ghost state construction that is defined and verified in its own file, [auth set](./program-proofs/auth_set.md).
