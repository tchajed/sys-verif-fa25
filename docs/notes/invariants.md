---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture
tags: literate
order: 17
shortTitle: "Lecture 17: Lock invariants"
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Lecture 17: Lock invariants

> Follow these notes in Rocq at [src/sys_verif/notes/invariants.v](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/src/sys_verif/notes/invariants.v).

In this lecture we'll introduce concurrent separation logic and lock invariants, our first tool for reasoning about concurrent programs.

## Learning outcomes

1. Understand how concurrent separation logic extends sequential separation logic.
2. Recall the rules for using lock invariants.

---

<!-- @include: ../notes/macros.snippet.md -->

## Motivation

We have concurrent programs with `go`, we modeled them with $\spawn$, now how do we prove something about them?

## Concurrent separation logic

Concurrent separation logic (CSL) extends separation logic to handle this new language where multiple threads can be running. What do we need to adapt? We need a way to reason about the new spawn construct, and we need to adapt the soundness theorem to talk about the new threadpool semantics.

### Soundness

Let's start with soundness:

**Definition** (_CSL soundness_): For some pure $Φ(v)$ (a Prop), if $\hoare{P}{e}{\fun{v} Φ(v)}$ and $([e], h) \leadsto_{tp} ([e'] \listapp T, h')$, then if $e'$ is an expression then $([e'] \listapp T, h')$ is not stuck, or $e' = v'$ for some value $v'$ and $Φ(v')$ holds. Furthermore, no thread in $T$ is stuck in $h'$.

This should look familiar to the definition of [pure soundness for sequential separation logic](/notes/sep-logic.md#soundness). We only use the threadpool semantics, and describe the return value of the main thread. The spawned threads are mostly ignored but we do state that none of them is stuck.

### Exercise: soundness for spawned threads

Suppose we omitted the last sentence of the soundness theorem, and defined $(T, h)$ to be stuck if _no_ threads could take a step. What program and specification $\hoare{P}{e}{Q}$ would be true under the alternate definition that wasn't with the real definition? Why does this motivate the stronger definition of soundness that we're actually using?

### Reasoning about spawn

The rule for reasoning about spawn is deceptively simple:

$$
\hoareV{\wp(e, \True)}{\spawn \, e}{\fun{v} \lift{v = ()}}
\eqnlabel{wp-spawn}
$$

Let's see a derived rule that's a little easier to explain:

$$
\dfrac{\hoare{P}{e'}{Q}}{
\hoare{\wp(e, \True) ∗ P}{\spawn \, e \then e'}{Q}
}
$$

Notice how we go from proving something about $\spawn \, e \then e'$ to proving a regular triple $\hoare{P}{e'}{Q}$ for the code after the spawn. To do so, we need to _separately_ prove that (a) $e$ is safe to run, with just the postcondition $\True$, and (b) establish the precondition for the rest of the code $e'$.

The proof of $\wp(e, \True)$ will in general consume some of the resources available, whatever should be owned initially by the background thread. These are basically lost, since the spawned thread never needs to "join" with the parent (unlike a more complex thread-creation mechanism), but we will later see how the spawned thread can communicate with the parent.

The resources $P$ need to be proven right away, unlike if we were verifying $e; e'$, since the scheduler could certainly choose to run $e'$ next (partly or even to completion). The postcondition of $Q$ makes sense for the whole construct because after spawning $e'$ takes over, and it establishes the postcondition $Q$.

Let's see this in action.

```rocq
From sys_verif.program_proof Require Import prelude empty_ffi.
From New.proof Require Import sync std.
From sys_verif.program_proof Require Import concurrent_init.

Section goose.
Context `{hG: !heapGS Σ}.
Context `{!globalsGS Σ} {go_ctx: GoContext}.

Let N := nroot .@ "lock".

Lemma wp_SetX (x_l: loc) (x: w64) :
  {{{ is_pkg_init concurrent ∗ x_l ↦ x }}}
    @! concurrent.SetX #x_l
  {{{ RET #(); x_l ↦ (W64 1) }}}.
Proof.
  wp_start as "x".
  wp_alloc x_l' as "x2".
  wp_auto.
  iApply "HΦ".
  iFrame.
Qed.

Lemma wp_NoGo :
  {{{ is_pkg_init concurrent }}}
    @! concurrent.NoGo #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "#init".
  wp_auto.
  wp_apply (wp_SetX with "[$x]").
  iIntros "x".
```

:::: info Goal

```txt
  Σ : gFunctors
  hG : heapGS Σ
  globalsGS0 : globalsGS Σ
  go_ctx : GoContext
  N := nroot.@"lock" : namespace
  Φ : val → iPropI Σ
  x_ptr : loc
  ============================
  _ : is_pkg_init concurrent
  "init" : emp
  --------------------------------------□
  "HΦ" : True -∗ Φ (# ())
  "x" : x_ptr ↦ W64 1
  --------------------------------------∗
  WP exception_do ((do: # ()) ;;;
                   return: # ()) {{ v, Φ v }}
```

::::

```rocq
  wp_pures.
  iApply "HΦ". done.
Qed.

Lemma wp_FirstGo :
  {{{ is_pkg_init concurrent }}}
    @! concurrent.FirstGo #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "#init".
  wp_auto.
  (* The actual GooseLang construct for creating threads is called Fork. The
  specification for Fork is equivalent to the wp-spawn above, but is written in
  continuation-passing style. *)
  wp_bind (Fork _).
  iApply (wp_fork with "[x]").
  { iModIntro.
    wp_pures.
    wp_apply (wp_SetX with "[$x]"). iIntros "x".
```

:::: info Goal

```txt
  Σ : gFunctors
  hG : heapGS Σ
  globalsGS0 : globalsGS Σ
  go_ctx : GoContext
  N := nroot.@"lock" : namespace
  Φ : val → iPropI Σ
  x_ptr : loc
  ============================
  _ : is_pkg_init concurrent
  "init" : emp
  --------------------------------------□
  "x" : x_ptr ↦ W64 1
  --------------------------------------∗
  WP exception_do ((do: # ()) ;;;
                   return: # ()) {{ _, True }}
```

::::

```rocq
    wp_pures.
    done.
  }
  iModIntro.
  wp_pures.
  iApply "HΦ". done.
Qed.

```

## Lock invariants

Recall the API for mutexes:

```go
new(sync.Mutex) // to create a new lock
func (m *sync.Mutex) Lock()
func (m *sync.Mutex) Unlock()
```

TODO: update explanation since init_Mutex fupd is now required

We can use mutexes (also commonly called locks) to ensure that critical sections of our code run atomically.

The way to reason about locked code in separation logic is via _lock invariants_. The intuition is that the program uses a lock to protect some memory, which will only be accessed with the lock held. We translate this idea to separation logic by associating a separation logic proposition called a lock invariant with each mutex. The proposition includes any memory protected by the lock; it can include any other separation logic propositions as well, which is what makes lock invariants both interesting and useful.

So what are the rules for lock invariants? The basic idea for the lock invariant $R$ associated with some mutex $\ell_m$ (which we're naming by the location of the pointer to that mutex) is that it is a separation logic assertion that holds whenever the lock is _free_. Because it holds when the lock is free, when a thread initially acquires the lock, it gets to assume $R$. Separation logic assertions are in general not duplicable, but because of mutual exclusion, a thread that acquires a mutex gets full ownership over $R$. However, when it wants to unlock the same mutex, it has to _give up_ ownership over $R$.

Formally, we have the following specification for Lock and Unlock:

$$
\hoare{\isLock(\ell_m, R)}{\operatorname{Lock} \, \ell_m}{R} \\

\hoare{\isLock(\ell_m, R) ∗ R}{\operatorname{Unlock} \,
\ell_m}{\True}
$$

To initially get $\isLock(\ell_m, R)$, which associates the lock invariant $R$ with the lock $\ell_m$, we have to use the following rule:

$$
\hoareV{R}{\operatorname{newMutex} \, ()}{\fun{v} ∃ \ell_m, v = \ell_m ∗ \isLock(\ell_m, R)}
$$

When we create a new mutex, we pick the lock invariant $R$ that represents what the mutex protects, and we also have to prove and give up $R$. This is what ensures the lock invariant holds initially.

An important aspect of this specification is that $\isLock(\ell_m, R)$ is _persistent_. This is needed since for mutexes to be useful, $\isLock(\ell_m, R)$ has to be available from multiple threads simultaneously. The fact that it is persistent also explains why we don't return it in the Lock and Unlock postconditions. Note that the assertion $\isLock(\ell_m, R)$ can safely be persistent even if $R$ is not persistent because it merely asserts that the lock invariant for the mutex $\ell_m$ is $R$; to actually get a copy of $R$, the thread has to call Lock, and the implementation of mutexes guarantees mutual exclusion at that point.

**Exercise:** Suppose we could somehow acquire $\isLock(\ell_m, R_1) ∗ \isLock(\ell_m, R_2)$ (notice these are the same mutex pointer), for arbitrarily chosen $R_1$ and $R_2$. What could go wrong?

Let's see our first example of using locks with Goose.

Code being verified:

```go
func FirstLock() uint64 {
	var x uint64
	m := new(sync.Mutex)
	go func() {
		m.Lock()
		x = 1
		m.Unlock()
	}()
	m.Lock()
	y := x
	m.Unlock()
	return y
}
```

Let's try a first proof that just shows this code is safe. Even with no interesting postcondition, the GooseLang model requires us to prove in this example that there are no race conditions on `x`; due to weak memory considerations, it isn't quite sound to model loads and stores of even a single variable as being atomic. The mutex in this example ensures the absence of races.

```rocq
Lemma wp_FirstLock_v1 :
  {{{ is_pkg_init concurrent }}}
    @! concurrent.FirstLock #()
  {{{ (y: w64), RET #y; True }}}.
Proof.
  wp_start as "_".
  wp_alloc_auto; wp_pures.
  wp_alloc_auto; wp_pures.
  wp_alloc r0_l as "r0". wp_auto.
  iMod (init_Mutex (∃ (y: w64), x_ptr ↦ y)%I with "r0 [$x]") as "#Hlock".
  iPersist "m".
  wp_bind (Fork _).
  iApply wp_fork.
  { iModIntro. wp_auto.
    wp_apply wp_Mutex__Lock.
    { iExact "Hlock". }
    iIntros "[Hlocked Hinv]".
```

:::: info Goal

```txt
  Σ : gFunctors
  hG : heapGS Σ
  globalsGS0 : globalsGS Σ
  go_ctx : GoContext
  N := nroot.@"lock" : namespace
  Φ : val → iPropI Σ
  x_ptr, m_ptr, r0_l : loc
  ============================
  _ : is_pkg_init concurrent
  "Hlock" : is_Mutex r0_l (∃ y : w64, x_ptr ↦ y)
  "m" : m_ptr ↦□ r0_l
  --------------------------------------□
  "Hlocked" : own_Mutex r0_l
  "Hinv" : ∃ y : w64, x_ptr ↦ y
  --------------------------------------∗
  WP exception_do
       ((do: # ()) ;;;
        let: "$r0" := # (W64 1) in
        (do: # x_ptr <-[# uint64T] "$r0") ;;;
        (do: method_call (# (ptrT.id sync.Mutex.id))
               (# "Unlock"%go) ![# ptrT] (# m_ptr)
               (# ())) ;;;
        return: # ())
  {{ _, True }}
```

::::

After calling Lock, the lock invariant appears in our hypotheses.

```rocq
    iNamed "Hinv".
    wp_auto.
    wp_apply (wp_Mutex__Unlock with "[Hlocked Hinv]").
    { iFrame "Hlock Hlocked".

```

To call Unlock, we need to prove the same lock invariant.

```rocq
      iModIntro.
```

:::: info Goal

```txt
  Σ : gFunctors
  hG : heapGS Σ
  globalsGS0 : globalsGS Σ
  go_ctx : GoContext
  N := nroot.@"lock" : namespace
  Φ : val → iPropI Σ
  x_ptr, m_ptr, r0_l : loc
  y : w64
  ============================
  _ : is_pkg_init concurrent
  "Hlock" : is_Mutex r0_l (∃ y0 : w64, x_ptr ↦ y0)
  "m" : m_ptr ↦□ r0_l
  --------------------------------------□
  "Hinv" : x_ptr ↦ W64 1
  --------------------------------------∗
  ∃ y0 : w64, x_ptr ↦ y0
```

::::

```rocq
      iFrame. }
    done. }
  iModIntro.
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hlock]"). iIntros "[Hlocked Hinv]". iNamed "Hinv".
  wp_auto.
  wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hinv]").
  iApply "HΦ". done.
Qed.

Lemma wp_FirstLock_v2 :
  {{{ is_pkg_init concurrent }}}
    @! concurrent.FirstLock #()
  {{{ (y: w64), RET #y; ⌜uint.Z y = 0 ∨ uint.Z y = 1⌝ }}}.
Proof.
  wp_start as "_".
  wp_alloc_auto; wp_pures.
  wp_alloc_auto; wp_pures.
  wp_alloc m_l as "Hm". wp_auto.
  iMod (init_Mutex (∃ (y: w64),
                  "x" :: x_ptr ↦ y ∗
                  "%Hx" :: ⌜uint.Z y = 0 ∨ uint.Z y = 1⌝)%I
         with "Hm [x]") as "#Hlock".
  { iModIntro. iFrame.
    iPureIntro. left; auto.
  }
  iPersist "m".
  wp_bind (Fork _).
  iApply wp_fork.
  { iModIntro. wp_auto.
    wp_apply wp_Mutex__Lock.
    { iExact "Hlock". }
    iIntros "[Hlocked Hinv]".
    iNamed "Hinv".
    wp_auto.
    wp_apply (wp_Mutex__Unlock with "[Hlocked x]").
    { iFrame "Hlock Hlocked".
      iModIntro.
      iFrame.
      iPureIntro. right; word.
    }
    done. }
  iModIntro.
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hlock]"). iIntros "[Hlocked Hinv]". iNamed "Hinv".
  wp_auto.
  wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $x]").
  { iPureIntro. auto. }
  iApply "HΦ". done.
Qed.

End goose.
```
