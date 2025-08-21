---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture
tags: literate
order: 20
shortTitle: "Lecture 20: Atomic specs"
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Lecture 20: Atomic specifications

> Follow these notes in Coq at [src/sys_verif/program_proof/atomic_specs.v](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/src/sys_verif/program_proof/atomic_specs.v).

## Learning outcomes

1. Explain how to specify an atomic data structure.
2. Prove and use atomic specs.

<!-- @include: ./macros.snippet.md -->

## Motivation

We've seen how to use ghost state to verify threads that are logically disjoint but physically interact with shared state (via a lock).

Now we'll turn our attention to _concurrent data structures_, in particular thread-safe data structures where operations are atomic. This is a common occurrence in concurrent libraries, and it will continue the same themes we saw with functional and imperative ADTs in the specification style.

## Example: atomic integer library

```go
type AtomicInt struct {
	x  uint64
	mu *sync.Mutex
}

func NewAtomicInt() *AtomicInt {
	return &AtomicInt{x: 0, mu: new(sync.Mutex)}
}

func (i *AtomicInt) Get() uint64 {
	i.mu.Lock()
	x := i.x
	i.mu.Unlock()
	return x
}

func (i *AtomicInt) Inc(y uint64) {
	i.mu.Lock()
	i.x += y
	i.mu.Unlock()
}
```

### Recall: sequential ADT

Let's remember what the spec would look like without concurrency, if there were no locks but also the integer didn't need to be shared between threads.

We would start with a predicate `int_rep (l: loc) (x: w64) : iProp Σ` that related a pointer to an integer in GooseLang to an abstract value. We choose to use `w64` as the abstract value, but it could also be `Z`; this spec has the advantage that it automatically guarantees the value of the integer is less than $2^{64}$. The predicate would be very simple: `int_rep l x := l ↦ x` would be enough.

Then the specification `wp_AtomicInt__Inc` would say

```
{{{ int_rep l x }}}
  AtomicInt__Inc l
{{{ RET #(); int_rep l (word.add x (W64 1))  }}}
```

(Recall that `word.add x (W64 1)` is the `w64` that comes from adding 1 to `x`. Its abstract value is only `uint.Z x + 1` if the addition doesn't overflow.)

### Atomic data structure specification

With a concurrent integer, we can no longer say precisely what the current value of the integer is if it is shared with other threads.

**Exercise:** why doesn't this work? Think through this before going forward.

::: details Solution

The value of the int might be `x` at exactly the time of the call, but then the following happens:

```
{l ↦ x0}
{l ↦ x1} (* other threads have run *)
l.mu.Lock()
l.x = l.x + 1
{l ↦ (word.add x1 (W64 1))}
l.mu.Unlock()
{l ↦ x2}
```

What we're seeing in this proof outline is that between the start of the call to `AtomicInt__Inc` and the time the lock is acquired, the int could change. Furthermore after unlocking but before the function returns, the int could change again.

:::

The situation may seem somewhat hopeless, but remember that there aren't actually arbitrary changes from other threads. Instead, the proof will share the integer with some protocol or invariant in mind, which threads will follow, much like how lock invariants work.

Let's see how this is realized in Coq for this example.

```rocq
From sys_verif.program_proof Require Import prelude empty_ffi.
From sys_verif.program_proof Require Import concurrent_init.

Module atomic_int.
Section proof.
Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.

```

This entire specification is based on an _representation predicate_ `P: w64 → iProp Σ`. The key to the spec is that `P` is chosen by the user at initialization time (see how in `wp_NewAtomicInt` the choice of `P` is left to the caller), then maintained by the specs for all the operations. At any given time `P x` will hold for the "current" value of the integer.

```rocq
#[local] Definition lock_inv (l: loc) (P: w64 → iProp Σ) : iProp _ :=
  ∃ (x: w64),
      "Hx" ∷ l ↦s[concurrent.AtomicInt :: "x"] x ∗
      "HP" ∷ P x.

(* The namespace of the lock invariant is only relevant when the lock is
acquired _from within an invariant_, which is an exceptional circumstance.
Hence we can just take the root namespace. *)
Definition N: namespace := nroot.

Definition is_atomic_int (l: loc) (P: w64 → iProp Σ): iProp _ :=
  ∃ (mu_l: loc),
  "mu" ∷ l ↦s[concurrent.AtomicInt :: "mu"]□ mu_l ∗
  "Hlock" ∷ is_Mutex mu_l (lock_inv l P).

(* This proof is automatic; we just assert it here. *)
#[global] Instance is_atomic_int_persistent l P : Persistent (is_atomic_int l P).
Proof. apply _. Qed.

Lemma wp_NewAtomicInt (P: w64 → iProp Σ) :
  {{{ is_pkg_init concurrent ∗ P (W64 0) }}}
    @! concurrent.NewAtomicInt #()
  {{{ (l: loc), RET #l; is_atomic_int l P }}}.
Proof.
  wp_start as "HP".
```

TODO: probably need to revise this in light of better support for mutex values.

In the previous lecture, we saw how `wp_new_free_lock` and `alloc_lock` split up the work of `wp_newMutex` into two steps: creating the memory for the lock and deciding on a lock invariant.

In the code for this library, the struct `AtomicInt` has a mutex and an integer. The mutex protects the memory for the integer field _of the same struct_. Thus we have almost no choice but to create the mutex before what it protects (the only other solution would be to create the struct with a `nil` mutex, then fill it in later, but this is rather unnatural code).

```rocq
  wp_alloc mu_ptr as "mu".
  wp_auto.
  wp_alloc l as "Hint".
  iApply struct_fields_split in "Hint".
  iNamed "Hint".
  cbn [concurrent.AtomicInt.x' concurrent.AtomicInt.mu'].
  iPersist "Hmu".
  iMod (init_Mutex (lock_inv l P) with "mu [$HP $Hx]") as "Hlock".
  wp_auto.
  iApply "HΦ".
  iFrame "#∗".
Qed.

```

It's helpful as a warmup for the specification of an operation to see a specification for `Inc` that just maintains the invariant that `P x` holds. **Note:** this is not the complete pattern; the real specification is given shortly.

To keep the lock invariant true while incrementing `x`, note that we will need to go from `P x` to `P (word.add x y`). Since `P` is a completely arbitrary predicate chosen by the caller, we need something from the caller to change anything about it. This takes the form of a ghost update, so the caller can update any ghost state associated with `P`.

The ghost update is a wand, and thus can only be used once by this specification. In exchange, it can use exclusive ghost state owned by the caller - we will see an example shortly when we use this spec.

There is one thing missing from this specification: if you only look at the specification, it could be proven by an implementation that does nothing! We will see a solution to this in the real specification for `Inc`.

```rocq
Lemma wp_AtomicInt__Inc_demo l (P: w64 → iProp _) (y: w64) :
  {{{ is_pkg_init concurrent ∗ is_atomic_int l P ∗
        (∀ x, P x -∗ |={⊤}=> P (word.add x y)) }}}
    l @ (ptrT.id concurrent.AtomicInt.id) @ "Inc" #y
  {{{ RET #(); True }}}.
Proof.
  wp_start as "[#Hint Hfupd]".
  iNamed "Hint".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hlock]").
  iIntros "[Hlocked Hinv]". iNamed "Hinv".

  (* critical section *)
  wp_auto.

  (* before we release the lock, we "fire" the user's fupd *)
  iMod ("Hfupd" with "HP") as "HP".

  wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked HP Hx]").
  { (* re-prove the lock invariant; this only works because the fupd changed
        [P] to [P (word.add x y)], and this matches the physical state of the
        variable. *)
    iFrame. }

  wp_pures.
  iApply "HΦ".
  done.
Qed.

```

The specification for `Get` doesn't need to change `P`. Instead, the user supplies an arbitrary postcondition `Q` and derives it from the current value of the integer in a ghost update.

This specification will undoubtedly be hard to read at first: you need to follow the path of all this higher-order code and track what the user of the specification is doing versus what this proof is doing.

```rocq
Lemma wp_AtomicInt__Get l (P: w64 → iProp _) (Q: w64 → iProp Σ) :
  {{{ is_pkg_init concurrent ∗
        is_atomic_int l P ∗ (∀ x, P x -∗ |={⊤}=> Q x ∗ P x) }}}
    l @ (ptrT.id concurrent.AtomicInt.id) @ "Get" #()
  {{{ (x: w64), RET #x; Q x }}}.
Proof.
  wp_start as "[#Hint Hfupd]".
  iNamed "Hint".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hlock]").
  iIntros "[Hlocked Hinv]". iNamed "Hinv".
  wp_auto.

  (* before we release the lock, we need to "fire" the user's fupd *)
  iMod ("Hfupd" with "HP") as "[HQ HP]".

  wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked HP Hx]").
  { iFrame. }

  wp_pures.
  iApply "HΦ".
  iFrame.
Qed.

```

### Exercise: executing the ghost update

In the proof above, we "executed" or "fired" the user-provided ghost update right before calling Unlock. What other point(s) in the proof would have worked?

---

To wrap up the AtomicInt spec we give the real specification for `Inc`, which combines the idea of changing the value of the integer with getting back a `Q x` that shows the update actually ran.

The postcondition looks much like for `Get`, in that it has `∃ x, Q x` for a caller-supplied `Q`. Unlike `Get`, that value `x` isn't returned, because that's not how this code works. But it's no issue for the proof to learn the value of the integer, even if the code doesn't have it.

```rocq
Lemma wp_AtomicInt__Inc l (P: w64 → iProp _) (Q: w64 → iProp Σ) (y: w64) :
  {{{ is_pkg_init concurrent ∗ is_atomic_int l P ∗
        (∀ x, P x -∗ |={⊤}=> Q x ∗ P (word.add x y)) }}}
    l @ (ptrT.id concurrent.AtomicInt.id) @ "Inc" #y
  {{{ (x: w64), RET #(); Q x }}}.
Proof.
  wp_start as "[#Hint Hfupd]".
  iNamed "Hint".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hlock]").
  iIntros "[Hlocked Hinv]". iNamed "Hinv".

  wp_auto.

  (* before we release the lock, we "fire" the user's fupd *)
  iMod ("Hfupd" with "HP") as "[HQ HP]".

  wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked HP Hx]").
  { iFrame. }

  iApply "HΦ".
  iFrame.
Qed.

End proof.
End atomic_int.

```

### Exercise: writing atomic specs

1. Write down an atomic specification for a `Dec` operation.
2. Write down a atomic specification for a version of `Inc` that returns the new value of the counter.

## Using atomic specs

The specification style is sometimes called HOCAP for "higher-order concurrent abstract predicates", from a [paper](https://kasv.dk/articles/hocap-tr.pdf) of the same name. The "concurrent" part is hopefully obvious; this whole thing is designed for concurrency. The "abstract predicates" part comes from the fact that we represent the data structure with an abstract predicate `P` that relates its current abstract state to an assertion (an `iProp`), which will presumably own ghost state. The "higher-order" part is due to the specification taking the representation predicate as an argument; that is, the `P` in the specs above is provided by the caller, not defined by the library.

Let's see an example of using the AtomicInt HOCAP specification, so that you can see how the caller will (a) pick `P` and (b) prove the ghost updates.

We'll return to the parallel add example.

```go
func ParallelAdd1() uint64 {
	i := NewAtomicInt()
	h1 := std.Spawn(func() {
		i.Inc(2)
	})
	h2 := std.Spawn(func() {
		i.Inc(2)
	})
	h1.Join()
	h2.Join()
	return i.Get()
}
```

This code is similar to what we saw in [ghost state](./ghost_state.md#proof-of-the-paralleladd-example); it's the same if you inline the code for the `AtomicInt`.

However, it is important that the locking that makes the integer atomic is all hidden in the `AtomicInt` library, and you will see that this proof does not involve any lock invariant. In fact, if we used atomic operations in Go's `sync/atomic` to implement the `AtomicInt` library, this proof would be none the wiser. This abstraction is really important when what we're hiding isn't a trivial library like `AtomicInt` but something complicated like a hash map or concurrent queue.

```rocq
Section proof.
Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.
Context `{ghost_varG0: ghost_varG Σ Z}.

```

As in the proof we saw before for `ParallelAdd3`, this proof will use two ghost variables, with the same meaning: $γ_1$ is the contribution from the first thread, while $γ_2$ is the contribution from the second. We'll relate them to the logical value of the atomic int with the abstraction predicate `int_rep γ1 γ2`; that is, where we saw `P` in the specs above, we'll now specialize to `int_rep γ1 γ2`.

```rocq
#[local] Definition int_rep γ1 γ2 : w64 → iProp Σ :=
  λ x,
    (∃ (x1 x2: Z),
    "Hx1" ∷ ghost_var γ1 (1/2) x1 ∗
    "Hx2" ∷ ghost_var γ2 (1/2) x2 ∗
    "%Hsum" ∷ ⌜x1 ≤ 2 ∧ x2 ≤ 2 ∧ uint.Z x = (x1 + x2)%Z⌝)%I.

Lemma wp_ParallelAdd1 :
  {{{ is_pkg_init concurrent }}}
    @! concurrent.ParallelAdd1 #()
  {{{ (x: w64), RET #x; ⌜uint.Z x = 4⌝ }}}.
Proof using ghost_varG0.
  wp_start as "_".
  wp_auto.
  (* Create the ghost variables first, since they are part of the atomic int's
  predicate. *)
  iMod (ghost_var_alloc 0) as (γ1) "[Hv1_1 Hx1_2]".
  iMod (ghost_var_alloc 0) as (γ2) "[Hv2_1 Hx2_2]".
  wp_apply (atomic_int.wp_NewAtomicInt (int_rep γ1 γ2)
            with "[Hv1_1 Hv2_1]").
  { iExists 0, 0. iFrame.
    iPureIntro.
    split; [ lia | ].
    split; [ lia | ].
    reflexivity. }
  iIntros (l) "#Hint".
  wp_auto.
  iPersist "i".

  (* This postcondition is the same. *)
  wp_apply (std.wp_Spawn (ghost_var γ1 (1/2) 2) with "[Hx1_2]").
  { clear Φ.
    iRename "Hx1_2" into "Hx".
    iIntros (Φ) "HΦ".
    wp_auto.

```

This is the most interesting part of the proof. We need to supply a postcondition `Q` here for what we expect the result of incrementing to be. Because we already own `ghost_var γ1 (1/2) 0`, we know that afterward we'll be able to increment that variable and obtain `ghost_var γ1 (1/2) 2`. To prove the ghost update in the Inc precondition, we'll supply a `with` clause that includes half ownership of `γ1`; this is required so that we have full ownership of `γ1` in order to change its value.

```rocq
    wp_apply (atomic_int.wp_AtomicInt__Inc _ _
                (λ _, ghost_var γ1 (1/2) 2) with "[$Hint Hx]").
    { iIntros (x) "Hrep".
      iNamed "Hrep".
```

:::: info Goal

```txt
  Σ : gFunctors
  hG : heapGS Σ
  globalsGS0 : globalsGS Σ
  go_ctx : GoContext
  ghost_varG0 : ghost_varG Σ Z
  i_ptr : loc
  γ1, γ2 : gname
  l, h1_ptr : loc
  Φ : val → iPropI Σ
  x : w64
  x1, x2 : Z
  Hsum : x1 ≤ 2 ∧ x2 ≤ 2 ∧ uint.Z x = x1 + x2
  ============================
  _ : is_pkg_init concurrent
  "Hint" : atomic_int.is_atomic_int l (int_rep γ1 γ2)
  "i" : i_ptr ↦□ l
  --------------------------------------□
  "Hx" : ghost_var γ1 (1 / 2) 0
  "Hx1" : ghost_var γ1 (1 / 2) x1
  "Hx2" : ghost_var γ2 (1 / 2) x2
  --------------------------------------∗
  |={⊤}=> ghost_var γ1 (1 / 2) 2 ∗ int_rep γ1 γ2 (word.add x (W64 2))
```

::::

```rocq
      iDestruct (ghost_var_agree with "Hx1 Hx") as %->.
      iMod (ghost_var_update_2 2 with "Hx1 Hx") as "[Hx1 Hx]".
      { rewrite Qp.half_half //. }
      iModIntro.
      iFrame.
      iPureIntro.
      split; [ lia | ].
      split; [ lia | ].
      word. }
    iIntros (_) "Hx". wp_pures.
    iApply "HΦ". iFrame. }
  iIntros (h1) "Hh1".
  wp_auto.

  wp_apply (std.wp_Spawn (ghost_var γ2 (1/2) 2) with "[Hx2_2]").
  { clear Φ.
    iRename "Hx2_2" into "Hx".
    iIntros (Φ) "HΦ".
    wp_auto.
    wp_apply (atomic_int.wp_AtomicInt__Inc _ _
                (λ _, ghost_var γ2 (1/2) 2) with "[$Hint Hx]").
    { iIntros (x) "Hrep".
      iNamed "Hrep".
      iDestruct (ghost_var_agree with "Hx2 Hx") as %->.
      iMod (ghost_var_update_2 2 with "Hx2 Hx") as "[Hx Hx2_2]".
      { rewrite Qp.half_half //. }
      iModIntro.
      iFrame.
      iPureIntro.
      split; [ lia | ].
      split; [ lia | ].
      word. }
    iIntros (_) "Hx". wp_pures.
    iApply "HΦ". iFrame. }
  iIntros (h2) "Hh2".
  wp_auto.
  wp_apply (std.wp_JoinHandle__Join with "[$Hh1]").
  iIntros "Hx1_2".
  wp_auto.
  wp_apply (std.wp_JoinHandle__Join with "[$Hh2]").
  iIntros "Hx2_2".
  wp_auto.
  wp_apply (atomic_int.wp_AtomicInt__Get _ _
              (λ x, ⌜uint.Z x = 4⌝)%I
            with "[$Hint Hx1_2 Hx2_2]").
    { iIntros (x) "Hrep".
      iNamed "Hrep".
      iDestruct (ghost_var_agree with "Hx1 Hx1_2") as %->.
      iDestruct (ghost_var_agree with "Hx2 Hx2_2") as %->.
      iModIntro.
      iFrame.
      iPureIntro.
      repeat split; try word. }
    iIntros (x Hx).
    wp_auto.
    iApply "HΦ".
    auto.
Qed.
End proof.
```
