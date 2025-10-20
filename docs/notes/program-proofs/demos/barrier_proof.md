---
# Auto-generated from literate source. DO NOT EDIT.
category: demo
tags: literate
order: -1
shortTitle: "Demo: barrier proof"
---

# Demo: specifying and verifying a concurrent barrier

> The Rocq code for this file is at [src/sys_verif/program_proof/demos/barrier_proof.v](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/src/sys_verif/program_proof/demos/barrier_proof.v).

The proof is divided into a few different logical phases:

1. Constructing any required resource algebras. We will use `auth_set` from [auth_set.v](./auth_set.md) (which we define just for this proof, but which is potentially reusable), and an existing library from Iris called `saved_prop`.
2. Defining the library's invariants and representation predicates, which also involves deciding how it will use ghost state.
3. Proving rules for ghost updates on the library-specific ownership predicates.
4. Program proofs that call the ghost updates as appropriate and do all of the code-specific reasoning.

You should read the code for auth_set to see how that ghost state works.

The other required ghost state is `saved_prop`. A saved proposition behaves like a `ghost_var` of type `iProp Σ`; this is all you need to know to read the code below.

::: details Why do we need saved_prop?

The reason there is a separate (and more sophisticated) library is related to the `Σ` in `iProp Σ` that we have been ignoring. This argument gives the set of resource algebras available for use in this iProp. This creates a circularity in trying to have `ghost_var γ (x: iProp Σ) : iProp Σ`; how would we define `Σ` in such a way that it contains the RA for ghost variables of type `iProp Σ`? Saved propositions resolve this circularity in a way that doesn't produce a paradox (along the lines of Russell's paradox). The only caveat is some uses of the ▷ modality which we will mostly ignore.

:::

```rocq
From iris.base_logic.lib Require Import saved_prop.
From sys_verif.program_proof Require Import demos.auth_set.
From sys_verif.program_proof Require Import prelude empty_ffi.
From New.proof Require Import std sync.
From New.generatedproof.sys_verif_code Require Export concurrent.barrier.


Section proof.
  Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
  Context {go_ctx: GoContext}.

  #[global] Instance : IsPkgInit barrier := define_is_pkg_init True%I.
  #[global] Instance : GetIsPkgInitWf barrier := build_get_is_pkg_init_wf.
End proof.


Module barrier.
Record barrier_names :=
  { recv_prop_name: gname;
    send_names_name: gname;
  }.

(* Boilerplate setup for ghost state required. You can safely ignore anything
related to [Σ] as an Iris technicality. *)
Class barrierG Σ := BarrierG {
    barrier_saved_propG :: savedPropG Σ;
    barrier_auth_setG :: auth_setG Σ gname;
  }.

Definition barrierΣ: gFunctors :=
  #[ savedPropΣ; auth_setΣ gname ].

#[global] Instance subG_barrierG Σ : subG barrierΣ Σ → barrierG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.
  Context `{!barrierG Σ}.

```

## Barrier predicates and invariants

This section of the proof constructs `is_barrier` and the predicates `send` and `recv` used by the specification. The barrier's specification is slightly unusual in that `is_barrier l γ` only relates the barrier's physical location to ghost names, and the rest of the specification is about `send γ P` and `recv γ Q` which are connected to the barrier only via those names.

The core of the barrier's representation predicate `is_barrier` is `own_barrier_ghost`, which owns all of the ghost state related to one barrier. For reading comprehension it may help to first skip ahead and read the rest of the predicate setup to see how `own_barrier_ghost` is used.

---

The lock invariant of the barrier relates the ghost state (via the names in `γ`) to `numWaiting`, the only physical state of the barrier.

The barrier uses two ghost variables, whose names are stored in γ:

`γ.(recv_prop_name)` is a saved proposition that records the proposition `Q` in whatever `recv γ Q` we've handed out. It will start out as `emp`, grow as we call `b.Add(1)`, and get reset to `emp` after `b.Wait()`.

`γ.(send_names_name)` is an `auth_set gname` tracking a _set of ghost names_, each of which records a proposition in a `send γ P` that we've handed out (_not_ the `γ` itself, which is about which barrier this `send` is for; you might want to skip ahead to read the definition of `send`). Only the sends that we're still waiting for our in this set; as those threads call `b.Done()`, the corresponding name is removed from the `auth_set`.

```rocq
  Definition own_barrier_ghost (γ: barrier_names) (num_waiting: w64)
    : iProp Σ :=
    (* The values of all the ghost state are existentially quantified since the
    caller interacts with them via ghost state: the [recv] predicate for [recvQ]
    and [send] predicates for the names in [sendNames] for the names in
    [sendNames]. *)
    ∃ (recvQ: iProp Σ) (sendNames: gset gname),
```

This ghost ownership owns only half of `γ.(recv_prop_name)`; the other half is controlled by `recv γ Q`. This division into two halves, one in a lock invariant and one owned by a thread, is a common pattern; we already saw it in the ParallelAdd example's ghost variables.

```rocq
    "recvQ" ∷ saved_prop_own γ.(recv_prop_name) (DfracOwn (1/2)) recvQ ∗
```

The number of `send` names (and thus number of predicates) is the number of waiting threads. An important consequence is that if `num_waiting = W64 0`, then there are no sendNames, and thus all threads have finished.

```rocq
    "%HnumWaiting" ∷ ⌜size sendNames = uint.nat num_waiting⌝ ∗
    "HsendNames_auth" ∷ auth_set_auth γ.(send_names_name) sendNames ∗
```

This is the most important and most complex part of the ghost state. A useful bit of context is that whenever we create a `γS ∈ sendNames`, it will be used for a saved proposition, and it will be persisted into a read-only saved proposition (we never change the proposition of a given `send γ P`).

The effect of writing `∃ P, saved_prop_own γS DfracDiscarded P` is to "read" the value of γS as `P`, since ownership of the ghost variable means we know its value is `P`. We also have `∗ ▷ P` which asserts ownership over (later) P. Then all of this business implies `recvQ`, the value of `γ.(recv_prop_name)`.

Two extremes are worth thinking about here. First, once we've created all the `send γ P` assertions, this wand says that the conjunction of those `P`s implies `recvQ`; this checks out since when we create `P` we add it onto the current `recv γ Q`. Second, when all the sends are complete (all threads have finished and called `b.Done()`), then the left-hand side of this wand will be simply `emp` and the lock invariant will own `recvQ`. That's exactly how we'll produce `Q` as the postcondition in `b.Done()` once `num_waiting = W64 0`.

```rocq
    "HrecvQ_wand" ∷ (([∗ set] γS ∈ sendNames,
                        ∃ P, saved_prop_own γS DfracDiscarded P ∗ ▷ P) -∗
                      ▷ recvQ).

  Definition lock_inv (l: loc) (γ: barrier_names) : iProp Σ :=
    ∃ (numWaiting: w64),
      "numWaiting" ∷ l ↦s[barrier.Barrier :: "numWaiting"] numWaiting ∗
      "Hbar" ∷ own_barrier_ghost γ numWaiting.

  Definition is_barrier (l: loc) (γ: barrier_names): iProp Σ :=
    ∃ (mu_l cond_l: loc),
      "#mu" ∷ l ↦s[barrier.Barrier :: "mu"]□ mu_l ∗
      "#cond" ∷ l ↦s[barrier.Barrier :: "cond"]□ cond_l ∗
      "#Hcond" ∷ is_Cond cond_l (interface.mk (ptrT.id sync.Mutex.id) #mu_l) ∗
      "#Hlock" ∷ is_Mutex (mu_l) (lock_inv l γ).

  #[global] Instance is_barrier_persistent l γ : Persistent (is_barrier l γ) := _.

  Definition send (γ: barrier_names) (P: iProp Σ): iProp Σ :=
    ∃ γS, auth_set_frag γ.(send_names_name) γS ∗
          saved_prop_own γS DfracDiscarded P.

  Definition recv (γ: barrier_names) (Q: iProp Σ): iProp Σ :=
    ∃ Q', saved_prop_own γ.(recv_prop_name) (DfracOwn (1/2)) Q' ∗
          (Q' -∗ Q).

  #[global] Instance recv_proper : Proper ((=) ==> (≡) ==> (≡)) recv.
  Proof.
    intros γ _ <- Q1 Q2 Heq.
    rewrite /recv.
    setoid_rewrite Heq; done.
  Qed.

  Lemma recv_mono γ Q Q' :
    (Q -∗ Q') -∗
    (recv γ Q -∗ recv γ Q').
  Proof.
    iIntros "Hwand Hrecv".
    iDestruct "Hrecv" as (Q'') "[Hsaved Hwand2]".
    iFrame "Hsaved".
    iIntros "H". iApply "Hwand". iApply "Hwand2". iFrame.
  Qed.

```

## Barrier ghost state updates

In this section we show how the custom ghost state defined for this library is updated, in ways that correspond to the physical operations. Its good for proof organization to factor this reasoning out to lemmas and separate it from reasoning about the code.

```rocq
  Lemma own_barrier_ghost_alloc :
    ⊢ |={⊤}=> ∃ γ, own_barrier_ghost γ (W64 0) ∗ recv γ emp.
  Proof.
    iMod (saved_prop_alloc emp (DfracOwn 1)) as (γrecv_prop) "Hrecv".
    { done. }
    iMod (auth_set_init (A:=gname)) as (γpending_sends) "HsendNames".
    set (γ := {| recv_prop_name := γrecv_prop;
                send_names_name := γpending_sends;
              |}).
    iDestruct "Hrecv" as "[Hrecv1 Hrecv2]".
    iModIntro.
    iAssert (recv γ emp) with "[$Hrecv2]" as "Hrecv_tok".
    { auto with iFrame. }
    iExists (γ); iFrame.
    auto with iFrame.
  Qed.

```

This is the change used for `b.Add(1)`. Observe how it changes the `recvQ` to append `∗ P`, and can create a new send name because we increment `num_waiting`.

```rocq
  Lemma own_barrier_ghost_add1 P γ Q num_waiting :
    uint.Z num_waiting + 1 < 2^64 →
    own_barrier_ghost γ num_waiting ∗ recv γ Q ={⊤}=∗
    own_barrier_ghost γ (word.add num_waiting (W64 1)) ∗
    ▷ recv γ (Q ∗ P) ∗
    send γ P.
  Proof.
    iIntros (Hno_overflow) "[Hbar Hrecv]".
    iNamed "Hbar".
    iDestruct "Hrecv" as (Q') "[recvQ2 HQwand]".
    iDestruct (saved_prop_agree with "recvQ recvQ2") as "#HQeq".
    iMod (saved_prop_update_halves (P ∗ recvQ) with "recvQ recvQ2")
      as "[recvQ recvQ2]".
    (* Allocating the new [send] saved proposition name is somewhat subtle: it
    needs to be different from any other (in-use) saved proposition. Since set
    available ghost names is infinite but the used names [sendNames] is finite,
    it's always possible to allocate such a name, and there's a "cofinite"
    allocation lemma to do just this. *)
    iMod (saved_prop_alloc_cofinite sendNames P DfracDiscarded)
      as (γS) "[%Hfresh #Hsend]".
    { done. }
    iMod (auth_set_alloc γS with "HsendNames_auth") as "[HsendNames_auth HγS]".
    { set_solver. }
    iModIntro.
    iAssert (send γ P) with "[$HγS $Hsend]" as "$".
    iAssert (▷ recv γ (Q ∗ P))%I with "[HQwand $recvQ2]" as "Hrecv".
    { iModIntro.
      iRewrite "HQeq".
      iIntros "[$ HQ]".
      iApply "HQwand"; iFrame. }
    iSplitR "Hrecv"; [ | iFrame ].
    iExists _, _; rewrite /named; iFrame.
    iSplit.
    - iPureIntro.
      rewrite size_union; [ set_solver | ].
      rewrite size_singleton.
      word.
    - rewrite /named.
      rewrite big_sepS_union; [ set_solver | ].
      rewrite big_sepS_singleton.
      iIntros "[(%P' & #HPsaved & HP') Hpending]".
      iDestruct ("HrecvQ_wand" with "Hpending") as "$".
      iDestruct (saved_prop_agree with "Hsend HPsaved") as "Hagree".
      iModIntro.
      iRewrite "Hagree"; iFrame.
  Qed.

  (* we can prove that owning [send γ P] implies that a thread is waiting, since
  it implies that there is a [γS ∈ sendNames] and [numWaiting] is the size of
  [sendNames]. *)
  Lemma own_barrier_ghost_send_waiting γ numWaiting P :
    own_barrier_ghost γ numWaiting ∗ send γ P -∗
    ⌜0 < uint.Z numWaiting⌝.
  Proof.
    iIntros "[Hbar HsendP]".
    iNamed "Hbar".
    iDestruct "HsendP" as (γS) "[HγS_frag HγS_P]".
    iDestruct (auth_set_elem with "HsendNames_auth HγS_frag") as %HγS_in_names.
    iPureIntro.
    destruct (decide (size sendNames = 0))%nat as [Heq0|]; [ | ].
    - exfalso.
      apply size_empty_inv in Heq0.
      set_solver.
    - word.
  Qed.

```

This is the update used for `b.Done()`. It consumes a `send γ P` and absorbs it into the ghost state along with `P`. What's happening here is that `HrecvQ_wand` is obtaining ownership over the `P` so that it can prove `recvQ` even with fewer send names on the left-hand side. (This is probably the most conceptually complicated part of the proof.)

```rocq
  Lemma own_barrier_ghost_send γ numWaiting P :
    own_barrier_ghost γ numWaiting ∗ send γ P ∗ P ={⊤}=∗
    own_barrier_ghost γ (word.sub numWaiting (W64 1)).
  Proof.
    iIntros "(Hbar & HsendP & HP)".
    iNamed "Hbar".
    iDestruct "HsendP" as (γS) "[HγS_frag HγS_P]".
    iDestruct (auth_set_elem with "HsendNames_auth HγS_frag") as %HγS_in_names.
    iMod (auth_set_dealloc with "[$HsendNames_auth $HγS_frag]") as "HsendNames_auth".
    iModIntro.
    iFrame "HsendNames_auth ∗".
    iSplit.
    - iPureIntro.
      rewrite size_difference; [ set_solver | ].
      rewrite size_singleton.
      assert (0 < uint.Z numWaiting); [ | word ].
      destruct (decide (size sendNames = 0))%nat as [Heq0|]; [ exfalso | lia ].
      apply size_empty_inv in Heq0.
      set_solver.
    - iIntros "HPs_except".
      iApply "HrecvQ_wand".
      iApply (big_sepS_delete _ _ γS).
      { auto. }
      iFrame "HPs_except".
      iFrame "HγS_P HP".
  Qed.

```

This is the update for `b.Done()`. We know `recvQ` in the invariant is `Q`, and need to return it. The `HrecvQ_wand` part of the lock invariant must be a proof of `recvQ`, because we know we're not waiting for any more threads. The only remaining complication is how to extract that `Q`. We use a common trick in concurrency proofs: we simultaneously change the receive predicate to the trivial `emp` and extract `▷Q`.

```rocq
  Lemma own_barrier_ghost_recv γ numWaiting Q :
    uint.Z numWaiting = 0 →
    own_barrier_ghost γ numWaiting ∗ recv γ Q ={⊤}=∗
    own_barrier_ghost γ numWaiting ∗ recv γ emp ∗ ▷Q.
  Proof.
    iIntros (Hzero) "[Hbar Hrecv]".
    iNamed "Hbar".
    iDestruct "Hrecv" as (Q') "[recvQ2 HQwand]".
    iDestruct (saved_prop_agree with "recvQ recvQ2") as "#HQeq".
    assert (sendNames = ∅); subst.
    { assert (sendNames ≡ ∅) by (apply size_empty_inv; lia).
      set_solver. }
    rewrite big_sepS_empty.
    iDestruct ("HrecvQ_wand" with "[$]") as "HrecvQ".
    (* we set the receive proposition to empty to be able to close the invariant *)
    iMod (saved_prop_update_halves emp with "recvQ recvQ2")
      as "[recvQ recvQ2]".
    iModIntro.
    iFrame "recvQ recvQ2".
    iSplitR "HQwand HrecvQ".
    { iFrame "∗".
      rewrite big_sepS_empty.
      auto with iFrame. }
    iSplit; [ auto with iFrame | ].
    iModIntro.
    iRewrite "HQeq" in "HrecvQ".
    iApply "HQwand"; iFrame.
  Qed.

```

With these ghost updates proven, we can treat [own_barrier_ghost] as opaque for the last section.

```rocq
  Typeclasses Opaque own_barrier_ghost send recv.

```

## Program proofs

Finally, we do all the program proofs, the specifications for each function. The hard work has all been done in the definition of the predicates and the lemmas for the ghost updates, so these proofs are mostly boilerplate.

```rocq
  Lemma wp_New :
    {{{ is_pkg_init barrier }}}
      @! barrier.New #()
    {{{ (l: loc) γ, RET #l; is_barrier l γ ∗ recv γ emp }}}.
  Proof.
    wp_start as "_".
    rewrite -wp_fupd.
    wp_auto. wp_alloc mu_l as "Hlock". wp_auto.

    wp_apply (wp_NewCond) as "%c His_cond".
    wp_alloc l as "Hbarrier".
    iApply struct_fields_split in "Hbarrier". iNamed "Hbarrier".
    cbn [barrier.Barrier.numWaiting' barrier.Barrier.mu' barrier.Barrier.cond'].
    wp_auto.

    iMod (own_barrier_ghost_alloc) as (γ) "[Hbar Hrecv]".
    iMod (init_Mutex (lock_inv _ γ)
           with "Hlock [$Hbar $HnumWaiting]") as "His_lock".
    iPersist "Hmu Hcond".
    iModIntro.
    iApply "HΦ".
    iFrame "#∗".
  Qed.

  Lemma wp_Barrier__Add1 (P: iProp Σ) (Q: iProp Σ) γ l :
    {{{ is_pkg_init barrier ∗ is_barrier l γ ∗ recv γ Q }}}
      l @ (ptrT.id barrier.Barrier.id) @ "Add" #(W64 1)
    {{{ RET #(); send γ P ∗ recv γ (Q ∗ P) }}}.
  Proof.
    wp_start as "[#Hbar Hrecv]".
    iNamed "Hbar".
    wp_auto.
    wp_apply (wp_Mutex__Lock with "[$Hlock]") as "[Hlocked Hinv]".
    iNamed "Hinv".

    wp_auto.
    wp_apply wp_SumAssumeNoOverflow. iIntros (Hno_overflow).
    wp_auto.

    iMod (own_barrier_ghost_add1 P with "[$Hbar $Hrecv]") as "(Hbar & Hrecv & Hsend)".
    { word. }

    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hbar $numWaiting]").
    iApply "HΦ". iFrame.
  Qed.

  Lemma wp_Barrier__Done γ l P :
    {{{ is_pkg_init barrier ∗ is_barrier l γ ∗ send γ P ∗ P }}}
      l @ (ptrT.id barrier.Barrier.id) @ "Done" #()
    {{{ RET #(); True }}}.
  Proof.
    wp_start as "(#Hbar & HsendP & HP)".
    iNamed "Hbar".
    wp_auto.
    wp_apply (wp_Mutex__Lock with "[$Hlock]") as "[Hlocked Hinv]".
    iNamed "Hinv".
    wp_auto.
    iPersist "b".
    wp_if_destruct.
    { (* The code checks if [numWaiting] is 0 and panics if so.

         In the proof we can show this is impossible using the ghost ownership,
       but it is still useful to have checks like this in code to catch misuse
       of the API in unverified code (or code not yet verified). *)
      iDestruct (own_barrier_ghost_send_waiting with "[$Hbar $HsendP]") as %HnumWaiting_gt_0.
      exfalso. move: HnumWaiting_gt_0. word. }
    iAssert (|={⊤}=> lock_inv l γ)%I with "[-Hlocked HΦ]" as ">Hlinv".
    { iMod (own_barrier_ghost_send with "[$Hbar $HsendP $HP]") as "Hbar".
      iModIntro.
      iFrame. }
    wp_if_destruct.
    - wp_apply (wp_Cond__Broadcast with "Hcond").
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hlinv]").
      iApply "HΦ". auto.
    - wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hlinv]").
      iApply "HΦ". auto.
  Qed.

  Lemma wp_Barrier__Wait γ l Q :
    {{{ is_pkg_init barrier ∗ is_barrier l γ ∗ recv γ Q }}}
      l @ (ptrT.id barrier.Barrier.id) @ "Wait" #()
    {{{ RET #(); Q ∗ recv γ emp }}}.
  Proof.
    wp_start as "(#Hbar & HrecvQ)".
    iNamed "Hbar".
    wp_auto.
    wp_apply (wp_Mutex__Lock with "[$Hlock]"). iIntros "[Hlocked Hinv]".
    wp_auto.

    iAssert (
          "Hlocked" ∷ own_Mutex mu_l ∗
          "Hinv" ∷ lock_inv l γ ∗
          "HQ" ∷ recv γ Q
          )%I
           with "[$Hlocked $Hinv $HrecvQ]" as "HI".
    wp_for "HI".
    - iNamed "Hinv".
      wp_auto.
      wp_if_destruct.
      + wp_apply (wp_Cond__Wait with "[Hlocked numWaiting Hbar]").
        { iFrame "Hcond".
          iSplit.
          - iApply (Mutex_is_Locker with "[] Hlock").
            iPkgInit.
          - iFrame.
        }
        iIntros "[Hlocked Hinv]".
        wp_auto.
        wp_for_post.
        iFrame.
      + iMod (own_barrier_ghost_recv with "[$Hbar $HQ]") as "(Hbar & Hrecv & HQ)".
        { word. }
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hbar numWaiting]").
        { iFrame. }
        iApply "HΦ".
        iFrame.
  Qed.

End proof.

End barrier.

#[global] Typeclasses Opaque barrier.is_barrier barrier.send barrier.recv.
```
