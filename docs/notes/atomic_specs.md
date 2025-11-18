---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture-note
tags: literate
order: 20
shortTitle: "Atomic specs"
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Atomic specifications

> Follow these notes in Rocq at [src/sys_verif/notes/atomic_specs.v](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/src/sys_verif/notes/atomic_specs.v).

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

Let's remember what the spec would look like without concurrency. Suppose we re-implemented this code with the same API but with a struct `SequentialInt` with a single integer field `x` - no locks, and the caller would not be allowed to share the data structure between threads.

We would start with a predicate `int_rep (l: loc) (x: w64) : iProp Σ` that related a pointer to an integer in GooseLang to an abstract value. We choose to use `w64` as the abstract value, but it could also be `Z`; this spec has the advantage that it automatically guarantees the value of the integer is less than $2^{64}$. The predicate would be very simple: `int_rep l x := l ↦s[SequentialInt :: "x"] x` would be enough.

Then the specification for `wp_SequentialInt__Inc` would say

```
{{{ int_rep l x }}}
  SequentialInt__Inc l
{{{ RET #(); int_rep l (word.add x (W64 1))  }}}
```

(Recall that `word.add x (W64 1)` is the `w64` that comes from adding 1 to `x`. Its abstract value is only `uint.Z x + 1` if the addition doesn't overflow.)

### Atomic data structure specification

With a concurrent integer, we can no longer say precisely what the current value of the integer is if it is shared with other threads.

**Exercise:** why doesn't this work? Think through this before going forward.

::: details Solution

The value of the int might be `x0` at exactly the time of the call, but then the following happens:

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

The situation may seem somewhat hopeless, but remember that there aren't actually arbitrary changes from other threads. Instead, the proof will share the integer with some _protocol_ or _invariant_ in mind, which threads will follow; indeed the most interesting code will require cooperation of all threads using this shared variable.

Let's see how this is realized in Rocq for this example.

```rocq
From sys_verif.program_proof Require Import prelude empty_ffi.
From sys_verif.program_proof Require Import concurrent_init.
(* use Perennial's ghost var, which is more modern than the upstream one *)
From Perennial.algebra Require Import ghost_var.

Open Scope Z_scope.

Module atomic_int.
Section proof.
Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.
Context `{!ghost_varG Σ w64}.

Implicit Types (γ: gname).

```

There are a few moving pieces in this style of specification. First, an implementation detail that is helpful to remember is that we will store the logical state of the data structure in a ghost variable. The integer library will hand out a predicate `own_int γ x` that says the data structure's value is exactly `x`; this will be internally implemented as simply being (1/2) ownership of the state ghost variable, with name γ. The atomic int will also maintain an invariant `is_atomic_int γ l` that relates the data structure pointer `l` to that ghost variable, which will internally be a lock invariant protecting the other half of the logical state.

In general for other data structures, the `is_data_structure` predicate need not be based on lock invariants, and the caller need not worry about how it's implemented; it merely connects the physical state to the ghost variable being used to track it.

Remember that there are always two perspectives on a specification: what does it mean to implement it, and what does it mean to use it. Since we are working bottom up, we will start by seeing this proven, then see it used in a proof, but the latter is more important.

```rocq
Definition own_int γ (x: w64) :=
  ghost_var γ (DfracOwn (1/2)) x.

#[global] Opaque own_int.
#[local ] Transparent own_int.

(* Timeless is a technical property related to the later modality; you can ignore it here. *)
#[global] Instance own_int_timeless γ x : Timeless (own_int γ x).
Proof. apply _. Qed.

(* this is local because even the existence of this predicate is not important to the user *)
#[local] Definition lock_inv γ (l: loc) : iProp _ :=
  ∃ (x: w64),
      "Hx" ∷ l ↦s[concurrent.AtomicInt :: "x"] x ∗
      "Hauth" ∷ ghost_var γ (DfracOwn (1/2)) x.

Definition is_atomic_int γ (l: loc) : iProp _ :=
  ∃ (mu_l: loc),
  "mu" ∷ l ↦s[concurrent.AtomicInt :: "mu"]□ mu_l ∗
  "Hlock" ∷ is_Mutex mu_l (lock_inv γ l).

#[global] Opaque is_atomic_int.
#[local]  Transparent is_atomic_int.

(* This proof is automatic; we just assert it here. *)
#[global] Instance is_atomic_int_persistent l P : Persistent (is_atomic_int l P).
Proof. apply _. Qed.

Lemma wp_NewAtomicInt :
  {{{ is_pkg_init concurrent }}}
    @! concurrent.NewAtomicInt #()
  {{{ γ (l: loc), RET #l; is_atomic_int γ l ∗ own_int γ (W64 0) }}}.
Proof.
  wp_start as "HP".
  wp_alloc mu_ptr as "mu".
  wp_auto.
  wp_alloc l as "Hint".
  iApply struct_fields_split in "Hint".
  iNamed "Hint".
  cbn [concurrent.AtomicInt.x' concurrent.AtomicInt.mu'].
  iPersist "Hmu".
  iMod (ghost_var_alloc (W64 0)) as (γ) "Hown".
  iDestruct "Hown" as "[Hown Hauth]".
  iMod (init_Mutex (lock_inv γ l) with "mu [$Hauth $Hx]") as "Hlock".
  wp_auto.
  iApply "HΦ".
  iFrame "#∗".
Qed.

```

As a warmup, let's give Inc a specification that _doesn't_ show thread safety, but does promise functional correctness. The proof is non-trivial since we still use the same lock invariant.

```rocq
Lemma wp_AtomicInt__Inc_sequential_spec γ l (x y: w64) :
  {{{ is_pkg_init concurrent ∗ is_atomic_int γ l ∗
        own_int γ x }}}
    l @ (ptrT.id concurrent.AtomicInt.id) @ "Inc" #y
  {{{ RET #(); own_int γ (word.add x y) }}}.
Proof.
  wp_start as "[#Hint Hown]".
  iNamed "Hint".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hlock]").
  iIntros "[Hlocked Hinv]". iNamed "Hinv".

  (* critical section *)
  wp_auto.

  (* we will need the x from the user to agree with the x0 in the lock invariant to show that the new value is correct *)
  iDestruct (ghost_var_agree with "Hown Hauth") as %Heq; subst x0.
  (* before we release the lock, we need to update the ghost variable *)
  iMod (ghost_var_update_2 (word.add x y) with "Hauth Hown") as "[Hauth Hown]".
  { rewrite dfrac_op_own Qp.half_half //. }

  wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hauth Hx]").
  { (* re-prove the lock invariant; this only works because of the ghost var update *)
    iFrame. }

  wp_pures.
  iApply "HΦ".
  done.
Qed.

```

### Exercise: why is the spec above sequential?

Why isn't the specification above good enough? Why do we call it "sequential" and "not thread safe"?

Now we will give a real, concurrent specification for Get, using an _atomic update_.

The general form is that Get will not take direct ownership of `own_int γ x`, but instead take an atomic update provided by the caller that (a) proves `own_int γ x` (this is an obligation on the caller), and (b) using `own_int γ x` (this is something our proof will give back to the caller) proves an arbitrary user-defined postcondition `Q x`. When the function returns, we'll give `Q x`. The atomic update is special in that the whole process of retrieving `own_int γ x`, returning it, and proving `Q x` all have to happen at a _single instant in time_ in the code's execution (hence the _atomic_ in the name).

Due to the use of atomic updates, the caller will not have to give up `own_int γ x` for the entire duration of the `l.Get()` call, but only at the instant that the proof logically executes the operation.

Due to the user-supplied and arbitrary postcondition `Q`, the proof of Get really does have to do the operation and use the atomic update - it's the only way to get a proof of `Q x` where `x` is the return value of the function.

This specification will undoubtedly be hard to read at first: you will probably need to go back and forth between the proof steps, the intuition above, and even the use of this specification in the proof below.

```rocq
Lemma wp_AtomicInt__Get_triple γ l (Q: w64 → iProp Σ) :
  {{{ is_pkg_init concurrent ∗
  is_atomic_int γ l ∗
  |={⊤,∅}=> ∃ x, own_int γ x ∗ (own_int γ x ={∅,⊤}=∗ Q x) }}}
    l @ (ptrT.id concurrent.AtomicInt.id) @ "Get" #()
  {{{ (x: w64), RET #x; Q x }}}.
Proof.
  wp_start as "(#Hint & Hau)".
  iNamed "Hint".
  wp_auto.

  wp_apply (wp_Mutex__Lock with "[$Hlock]").
  iIntros "[Hlocked Hinv]". iNamed "Hinv".
  wp_auto.

  (* before we release the lock, we need to "fire" the user's fupd with [iMod]. *)
  iApply fupd_wp.
  iMod "Hau" as (x0) "[Hown Hclose]".
  iDestruct (ghost_var_agree with "Hauth Hown") as %Heq; subst x0.
  iMod ("Hclose" with "Hown") as "HQ".
  iModIntro.

  wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hauth Hx]").
  { iFrame. }

  iApply "HΦ".
  done.
Qed.

```

### Exercise: executing the ghost update

In the proof above, we "executed" or "fired" the user-provided ghost update right before calling Unlock. What other point(s) in the proof would have worked?

---

The specification above is a bit inconvenient since the caller needs to decide what the postcondition `Q` should be to call it. We can give a more convenient (but basically equivalent) specification by dropping down to weakest preconditions and not using the Hoare triple notation, which already have an arbitrary postcondition `Φ`.

```rocq
Lemma wp_AtomicInt__Get γ l :
  ∀ (Φ: val → iProp Σ),
  (is_pkg_init concurrent ∗
  is_atomic_int γ l ∗
  |={⊤,∅}=> ∃ x, own_int γ x ∗ (own_int γ x ={∅,⊤}=∗ Φ #x)) -∗
  WP l @ (ptrT.id concurrent.AtomicInt.id) @ "Get" #() {{ Φ }}.
Proof.
  (* wp_start doesn't support a specification like this (which isn't quite a Hoare triple) *)
  iIntros (Φ) "(#? & #Hint & Hau)".
  wp_method_call. wp_call.
  iNamed "Hint".
  wp_auto.

  (* from here the proof is the same: acquire the mutex, change the ghost var, release the mutex *)
  wp_apply (wp_Mutex__Lock with "[$Hlock]").
  iIntros "[Hlocked Hinv]". iNamed "Hinv".
  wp_auto.

  iApply fupd_wp.
  iMod "Hau" as (x0) "[Hown Hclose]".
  iDestruct (ghost_var_agree with "Hauth Hown") as %Heq; subst x0.
  iMod ("Hclose" with "Hown") as "HΦ".
  iModIntro.

  wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hauth Hx]").
  { iFrame. }

  iApply "HΦ".
Qed.

```

---

To wrap up the AtomicInt spec we give the real specification for `Inc`, which still requires the user to prove `∃ x, own_int γ x` but then gives back an updated predicate `own_int γ (word.add x (W64 2))`.

```rocq
Lemma wp_AtomicInt__Inc γ l (y: w64) :
  ∀ Φ,
  (is_pkg_init concurrent ∗ is_atomic_int γ l ∗
   |={⊤,∅}=> ∃ x, own_int γ x ∗ (own_int γ (word.add x y) ={∅,⊤}=∗ Φ #())) -∗
    WP l @ (ptrT.id concurrent.AtomicInt.id) @ "Inc" #y {{ Φ }}.
Proof.
  iIntros (Φ) "(#? & #Hint & Hau)".
  wp_method_call. wp_call.
  iNamed "Hint".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hlock]").
  iIntros "[Hlocked Hinv]". iNamed "Hinv".

  wp_auto.

  (* before we release the lock, we "fire" the user's fupd *)
  iApply fupd_wp.
  iMod "Hau" as (x0) "[Hown Hclose]".
  iDestruct (ghost_var_agree with "Hauth Hown") as %Heq; subst x0.
  iMod (ghost_var_update_2 (word.add x y) with "Hauth Hown") as "[Hauth Hown]".
  { rewrite dfrac_op_own Qp.half_half //. }
  iMod ("Hclose" with "Hown") as "HΦ".
  iModIntro.

  wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hauth Hx]").
  { iFrame. }

  iApply "HΦ".
Qed.

End proof.
End atomic_int.

```

### Exercise: writing atomic specs

1. Write down an atomic specification for a `Dec` operation.
2. Write down a atomic specification for a version of `Inc` that returns the new value of the counter.

## Using atomic specs

Let's see an example of using the AtomicInt specification, so that you can see how the caller will maintain `own_int γint x` and prove the atomic updates that show up in the Get and Inc preconditions.

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
Context `{ghost_varG0: ghost_varG Σ w64}.
Context `{ghost_varG1: ghost_varG Σ Z}.

Let N := nroot .@ "inv".

```

As in the proof we saw before for `ParallelAdd3`, this proof will use two ghost variables, with the same meaning: $γ_1$ is the contribution from the first thread, while $γ_2$ is the contribution from the second.

Unlike the proof before, which only used the one lock invariant, we will also use a regular _invariant_ to relate the state of the atomic integer to the ghost variables. Remember that the ParallelAdd3 code inlined the concurrency control for the integer (that is, the code explicitly used mutex operations around an ordinary local variable); this code delegates that to the atomic integer library. The proof will not take "know" that the atomic integer is protected by a mutex, so it will have to use an invariant, but the benefit is that the atomic integer could easily be replaced by a different implementation that didn't use a mutex (for example, using the Go [`atomic.Uint64`](https://pkg.go.dev/sync/atomic#Uint64) struct).

```rocq
#[local] Definition add_inv γint γ1 γ2 : iProp Σ :=
    (∃ (x: w64) (x1 x2: Z),
    "Hint" ∷ atomic_int.own_int γint x ∗
    "Hx1" ∷ ghost_var γ1 (DfracOwn (1/2)) x1 ∗
    "Hx2" ∷ ghost_var γ2 (DfracOwn (1/2)) x2 ∗
    "%Hsum" ∷ ⌜x1 ≤ 2 ∧ x2 ≤ 2 ∧ uint.Z x = (x1 + x2)%Z⌝)%I.

Lemma wp_ParallelAdd1 :
  {{{ is_pkg_init concurrent }}}
    @! concurrent.ParallelAdd1 #()
  {{{ (x: w64), RET #x; ⌜uint.Z x = 4⌝ }}}.
Proof using ghost_varG0 ghost_varG1.
  wp_start as "_".
  wp_auto.

  (* When we create the atomic int, we'll own it completely; only after that will we share it with an invariant. *)
  wp_apply (atomic_int.wp_NewAtomicInt).
  iIntros (γint l) "[#His_int Hint]".
```

:::: info Goal

```txt
  ghost_varG0 : ghost_varG Σ w64
  ghost_varG1 : ghost_varG Σ Z
  N := nroot.@"inv" : namespace
  Φ : val → iPropI Σ
  i_ptr : loc
  γint : gname
  l : loc
  ============================
  _ : is_pkg_init concurrent
  "His_int" : atomic_int.is_atomic_int γint l
  --------------------------------------□
  "HΦ" : ∀ x : w64, ⌜uint.Z x = 4⌝ -∗ Φ (# x)
  "i" : i_ptr ↦ default_val loc
  "Hint" : atomic_int.own_int γint (W64 0)
  --------------------------------------∗
  WP exception_do
       (let: "$r0" := # l in
        (do: # i_ptr <-[# ptrT] "$r0") ;;;
        let: "h1" := alloc (type.zero_val (# ptrT)) in
        let: "$r0" := let: "$a0" := λ: <>,
                                      exception_do
                                        ((do: (let: "$a0" :=
                                               # (W64 2) in
                                               method_call
                                                 (#
                                                 (ptrT.id
                                                 concurrent.AtomicInt.id))
                                                 (# "Inc"%go)
                                                 ![
                                                 # ptrT]
                                                 (# i_ptr) "$a0")) ;;;
                                         return: # ()) in
                      func_call (# std.Spawn) "$a0" in
        (do: "h1" <-[# ptrT] "$r0") ;;;
        let: "h2" := alloc (type.zero_val (# ptrT)) in
        let: "$r0" := let: "$a0" := λ: <>,
                                      exception_do
                                        ((do: (let: "$a0" :=
                                               # (W64 2) in
                                               method_call
                                                 (#
                                                 (ptrT.id
                                                 concurrent.AtomicInt.id))
                                                 (# "Inc"%go)
                                                 ![
                                                 # ptrT]
                                                 (# i_ptr) "$a0")) ;;;
                                         return: # ()) in
                      func_call (# std.Spawn) "$a0" in
        (do: "h2" <-[# ptrT] "$r0") ;;;
        (do: method_call (# (ptrT.id std.JoinHandle.id))
               (# "Join"%go) ![# ptrT] "h1" (# ())) ;;;
        (do: method_call (# (ptrT.id std.JoinHandle.id))
               (# "Join"%go) ![# ptrT] "h2" (# ())) ;;;
        return: method_call (# (ptrT.id concurrent.AtomicInt.id))
                  (# "Get"%go) ![# ptrT] (# i_ptr)
                  (# ()))
  {{ v, Φ v }}
```

::::

```rocq
  wp_auto.

  (* Create the ghost variables, then initialize the invariant. *)
  iMod (ghost_var_alloc 0) as (γ1) "[Hv1_1 Hx1_2]".
  iMod (ghost_var_alloc 0) as (γ2) "[Hv2_1 Hx2_2]".
  iMod (inv_alloc N _ (add_inv γint γ1 γ2) with "[Hint Hv1_1 Hv2_1]") as "#Hinv".
  {
    iModIntro.
    iFrame.
    done.
  }
  iPersist "i".

  (* This postcondition is the same. *)
  wp_apply (std.wp_Spawn (ghost_var γ1 (DfracOwn (1/2)) 2) with "[Hx1_2]").
  { clear Φ.
    iRename "Hx1_2" into "Hx".
    iIntros (Φ) "HΦ".
    wp_auto.
    wp_apply (atomic_int.wp_AtomicInt__Inc).
    iFrame "His_int".
    (* This boilerplate opens this invariant *)
    iInv "Hinv" as ">HI" "Hclose".
    iApply fupd_mask_intro; [ set_solver | iIntros "Hmask" ].
    iNamedSuffix "HI" "_inv".
```

:::: info Goal

```txt
  ghost_varG0 : ghost_varG Σ w64
  ghost_varG1 : ghost_varG Σ Z
  N := nroot.@"inv" : namespace
  i_ptr : loc
  γint : gname
  l, h1_ptr : loc
  γ1, γ2 : gname
  Φ : val → iPropI Σ
  x : w64
  x1, x2 : Z
  Hsum_inv : x1 ≤ 2 ∧ x2 ≤ 2 ∧ uint.Z x = x1 + x2
  ============================
  _ : is_pkg_init concurrent
  "His_int" : atomic_int.is_atomic_int γint l
  "Hinv" : inv N (add_inv γint γ1 γ2)
  "i" : i_ptr ↦□ l
  --------------------------------------□
  "Hx" : ghost_var γ1 (DfracOwn (1 / 2)) 0
  "HΦ" : ghost_var γ1 (DfracOwn (1 / 2)) 2 -∗ Φ (# ())
  "Hint_inv" : atomic_int.own_int γint x
  "Hx1_inv" : ghost_var γ1 (DfracOwn (1 / 2)) x1
  "Hx2_inv" : ghost_var γ2 (DfracOwn (1 / 2)) x2
  "Hclose" : ▷ add_inv γint γ1 γ2 ={⊤ ∖ ↑N,⊤}=∗ emp
  "Hmask" : |={∅,⊤ ∖ ↑N}=> emp
  --------------------------------------∗
  ∃ x0 : w64, atomic_int.own_int γint x0 ∗
    (atomic_int.own_int γint (word.add x0 (W64 2)) ={∅,⊤}=∗
     WP exception_do ((do: # ()) ;;;
                      return: # ()) {{ v, Φ v }})
```

::::

```rocq
    (* Prove atomic_int.own_int using the invariant contents, then get back own_int with the incremented value *)
    iFrame "Hint_inv". iIntros "Hint_inv".
    iMod "Hmask" as "_".
```

:::: info Goal

```txt
  ghost_varG0 : ghost_varG Σ w64
  ghost_varG1 : ghost_varG Σ Z
  N := nroot.@"inv" : namespace
  i_ptr : loc
  γint : gname
  l, h1_ptr : loc
  γ1, γ2 : gname
  Φ : val → iPropI Σ
  x : w64
  x1, x2 : Z
  Hsum_inv : x1 ≤ 2 ∧ x2 ≤ 2 ∧ uint.Z x = x1 + x2
  ============================
  _ : is_pkg_init concurrent
  "His_int" : atomic_int.is_atomic_int γint l
  "Hinv" : inv N (add_inv γint γ1 γ2)
  "i" : i_ptr ↦□ l
  --------------------------------------□
  "Hx" : ghost_var γ1 (DfracOwn (1 / 2)) 0
  "HΦ" : ghost_var γ1 (DfracOwn (1 / 2)) 2 -∗ Φ (# ())
  "Hx1_inv" : ghost_var γ1 (DfracOwn (1 / 2)) x1
  "Hx2_inv" : ghost_var γ2 (DfracOwn (1 / 2)) x2
  "Hclose" : ▷ add_inv γint γ1 γ2 ={⊤ ∖ ↑N,⊤}=∗ emp
  "Hint_inv" : atomic_int.own_int γint (word.add x (W64 2))
  --------------------------------------∗
  |={⊤ ∖ ↑N,⊤}=> WP exception_do ((do: # ()) ;;;
                                  return: # ()) {{ v, Φ v }}
```

::::

```rocq
    (* Now we need to restore the invariant to get the mask back to normal. *)
    iDestruct (ghost_var_agree with "Hx Hx1_inv") as %Heq; subst.
    iMod (ghost_var_update_2 2 with "Hx Hx1_inv") as "[Hx Hx1_inv]".
    { rewrite dfrac_op_own Qp.half_half //. }
    iMod ("Hclose" with "[Hint_inv Hx1_inv Hx2_inv]").
    { iFrame.
      iPureIntro.
      word. }

    (* prove postcondition after Inc finishes *)
    iModIntro.
```

:::: info Goal

```txt
  ghost_varG0 : ghost_varG Σ w64
  ghost_varG1 : ghost_varG Σ Z
  N := nroot.@"inv" : namespace
  i_ptr : loc
  γint : gname
  l, h1_ptr : loc
  γ1, γ2 : gname
  Φ : val → iPropI Σ
  x : w64
  x2 : Z
  Hsum_inv : 0 ≤ 2 ∧ x2 ≤ 2 ∧ uint.Z x = 0 + x2
  ============================
  _ : is_pkg_init concurrent
  "His_int" : atomic_int.is_atomic_int γint l
  "Hinv" : inv N (add_inv γint γ1 γ2)
  "i" : i_ptr ↦□ l
  --------------------------------------□
  "HΦ" : ghost_var γ1 (DfracOwn (1 / 2)) 2 -∗ Φ (# ())
  "Hx" : ghost_var γ1 (DfracOwn (1 / 2)) 2
  _ : emp
  --------------------------------------∗
  WP exception_do ((do: # ()) ;;;
                   return: # ()) {{ v, Φ v }}
```

::::

```rocq
    wp_auto.
    iApply "HΦ".
    iFrame. }
  iIntros (h1) "Hh1".
  wp_auto.

  (* the other thread has a copy-pasted proof *)
  wp_apply (std.wp_Spawn (ghost_var γ2 (DfracOwn (1/2)) 2) with "[Hx2_2]").
  { clear Φ.
    iRename "Hx2_2" into "Hx".
    iIntros (Φ) "HΦ".
    wp_auto.
    wp_apply (atomic_int.wp_AtomicInt__Inc).
    iFrame "His_int".

    (* open invariant *)
    iInv "Hinv" as ">HI" "Hclose".
    iApply fupd_mask_intro; [ set_solver | iIntros "Hmask" ].
    iNamedSuffix "HI" "_inv".

    iFrame "Hint_inv". iIntros "Hint_inv".
    iMod "Hmask" as "_".

    (* Now restore invariant *)
    iDestruct (ghost_var_agree with "Hx Hx2_inv") as %Heq; subst.
    iMod (ghost_var_update_2 2 with "Hx Hx2_inv") as "[Hx Hx2_inv]".
    { rewrite dfrac_op_own Qp.half_half //. }
    iMod ("Hclose" with "[Hint_inv Hx1_inv Hx2_inv]").
    { iFrame.
      iPureIntro.
      word. }

    (* postcondition *)
    iModIntro.
    wp_auto.
    iApply "HΦ".
    iFrame. }
  iIntros (h2) "Hh2".
  wp_auto.
  wp_apply (std.wp_JoinHandle__Join with "[$Hh1]").
  iIntros "Hx1_2".
  wp_auto.
  wp_apply (std.wp_JoinHandle__Join with "[$Hh2]").
  iIntros "Hx2_2".
  wp_auto.
  wp_apply (atomic_int.wp_AtomicInt__Get).
  iFrame "His_int".

  iInv "Hinv" as ">HI" "Hclose".
  iApply fupd_mask_intro; [ solve_ndisj | iIntros "Hmask" ].
  iNamedSuffix "HI" "_inv".
  iDestruct (ghost_var_agree with "Hx1_inv Hx1_2") as %->.
  iDestruct (ghost_var_agree with "Hx2_inv Hx2_2") as %->.
  iFrame "Hint_inv". iIntros "Hint_inv".
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[Hint_inv Hx1_inv Hx2_inv]").
  { iFrame. word. }

  iModIntro.
  wp_auto.
  iApply "HΦ".
  word.
Qed.
End proof.
```
