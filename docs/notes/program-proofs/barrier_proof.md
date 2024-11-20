---
# Auto-generated from literate source. DO NOT EDIT.
category: demo
tags: literate
order: -1
shortTitle: "Demo: barrier proof"
---

# Demo: specifying and verifying a concurrent barrier

> The Coq code for this file is at [src/sys_verif/program_proof/demos/barrier_proof.v](https://github.com/tchajed/sys-verif-fa24-proofs/blob/main/src/sys_verif/program_proof/demos/barrier_proof.v).

```coq
From iris.base_logic.lib Require Import saved_prop.
From Perennial.program_proof Require Import std_proof.

From sys_verif.program_proof.concurrent Require Import auth_set.

From Goose.sys_verif_code Require Import concurrent.

From sys_verif.program_proof Require Import prelude.

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
  Context `{hG: heapGS Σ, !ffi_semantics _ _, !ext_types _}.
  Context `{!barrierG Σ}.

  (* The lock invariant of the barrier relates the ghost state (via the names in
  [γ]) to [numWaiting], the only physical state of the barrier. *)
  Definition own_barrier_ghost (γ: barrier_names) (num_waiting: w64)
    : iProp Σ :=
    (* The values of all the ghost state are existentially quantified since the
    caller interacts with them via ghost state: the [recv] predicate for [recvQ]
    and [send] predicates for the names in [sendNames] for the names in
    [sendNames]. *)
    ∃ (recvQ: iProp Σ) (sendNames: gset gname),
    "recvQ" ∷ saved_prop_own γ.(recv_prop_name) (DfracOwn (1/2)) recvQ ∗
    "%HnumWaiting" ∷ ⌜size sendNames = uint.nat num_waiting⌝ ∗
    "HsendNames_auth" ∷ auth_set_auth γ.(send_names_name) sendNames ∗
    "HrecvQ_wand" ∷ (([∗ set] γS ∈ sendNames,
                        ∃ P, saved_prop_own γS DfracDiscarded P ∗ ▷ P) -∗
                      ▷ recvQ).

  Definition lock_inv (l: loc) (γ: barrier_names) : iProp Σ :=
    ∃ (numWaiting: w64),
      "numWaiting" ∷ l ↦[Barrier :: "numWaiting"] #numWaiting ∗
      "Hbar" ∷ own_barrier_ghost γ numWaiting.

  Definition is_barrier (l: loc) (γ: barrier_names): iProp Σ :=
    ∃ (mu_l cond_l: loc),
      "#mu" ∷ l ↦[Barrier :: "mu"]□ #mu_l ∗
      "#cond" ∷ l ↦[Barrier :: "cond"]□ #cond_l ∗
      "#Hcond" ∷ is_cond cond_l (#mu_l) ∗
      "#Hlock" ∷ is_lock nroot (#mu_l) (lock_inv l γ).

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
      rewrite size_union; [ | set_solver ].
      rewrite size_singleton.
      word.
    - rewrite /named.
      rewrite big_sepS_union; [ | set_solver ].
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

  (* delete [send γ P] and absorb it into the ghost state along with [P], to be
  used to prove [recvQ] when all threads are done *)
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
      rewrite size_difference; [ | set_solver ].
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

  (* with these ghost updates proven, we can treat [own_barrier_ghost] as opaque
  for the proofs of each function *)
  Typeclasses Opaque own_barrier_ghost send recv.

  Lemma wp_NewBarrier :
    {{{ True }}}
      NewBarrier #()
    {{{ (l: loc) γ, RET #l; is_barrier l γ ∗ recv γ emp }}}.
  Proof.
    wp_start as "_".
    rewrite -wp_fupd.
    wp_apply wp_new_free_lock. iIntros (mu_l) "Hlock".
    wp_apply (wp_newCond' with "Hlock"). iIntros (cond_l) "[Hlock Hcond]".
    wp_alloc l as "Hbarrier".
    iApply struct_fields_split in "Hbarrier". iNamed "Hbarrier".
    iMod (own_barrier_ghost_alloc) as (γ) "[Hbar Hrecv]".
    iMod (alloc_lock nroot _ _ (lock_inv _ γ)
           with "Hlock [$Hbar $numWaiting]") as "His_lock".
    iMod (struct_field_pointsto_persist with "mu") as "mu".
    iMod (struct_field_pointsto_persist with "cond") as "cond".

    iModIntro.
    iApply "HΦ".
    iFrame.
  Qed.

  Lemma wp_Barrier__Add1 (P: iProp Σ) (Q: iProp Σ) γ l :
    {{{ is_barrier l γ ∗ recv γ Q }}}
      Barrier__Add #l #(W64 1)
    {{{ RET #(); send γ P ∗ recv γ (Q ∗ P) }}}.
  Proof.
    wp_start as "[#Hbar Hrecv]".
    iNamed "Hbar".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "[$]"). iIntros "[Hlocked Hinv]".
    iNamed "Hinv".

    wp_pures.
    wp_loadField.
    wp_apply wp_SumAssumeNoOverflow. iIntros (Hno_overflow).
    wp_storeField.
    wp_loadField.

    iMod (own_barrier_ghost_add1 P with "[$Hbar $Hrecv]") as "(Hbar & Hrecv & Hsend)".
    { word. }

    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hbar $numWaiting]").
    wp_pures.
    iModIntro.
    iApply "HΦ". iFrame.
  Qed.

  Lemma wp_Barrier__Done γ l P :
    {{{ is_barrier l γ ∗ send γ P ∗ P }}}
      Barrier__Done #l
    {{{ RET #(); True }}}.
  Proof.
    wp_start as "(#Hbar & HsendP & HP)".
    iNamed "Hbar".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "[$]"). iIntros "[Hlocked Hinv]".
    iNamed "Hinv".
    wp_loadField.
    wp_if_destruct.
    { (* The code checks if [numWaiting] is 0 and panics if so.

         In the proof we can show this is impossible using the ghost ownership,
       but it is still useful to have checks like this in code to catch misuse
       of the API in unverified code (or code not yet verified). *)
      iDestruct (own_barrier_ghost_send_waiting with "[$Hbar $HsendP]") as %HnumWaiting_gt_0.
      exfalso. move: HnumWaiting_gt_0. word. }
    wp_loadField. wp_storeField. wp_loadField.
    iAssert (|={⊤}=> lock_inv l γ)%I with "[-Hlocked HΦ]" as ">Hlinv".
    { iMod (own_barrier_ghost_send with "[$Hbar $HsendP $HP]") as "Hbar".
      iModIntro.
      iFrame. }
    wp_if_destruct.
    - wp_loadField. wp_apply (wp_Cond__Broadcast with "Hcond").
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hlinv]").
      wp_pures.
      iModIntro. iApply "HΦ". auto.
    - wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hlinv]").
      wp_pures.
      iModIntro. iApply "HΦ". auto.
  Qed.

  Lemma wp_Barrier__Wait γ l Q :
    {{{ is_barrier l γ ∗ recv γ Q }}}
      Barrier__Wait #l
    {{{ RET #(); Q ∗ recv γ emp }}}.
  Proof.
    wp_start as "(#Hbar & HrecvQ)".
    iNamed "Hbar".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "[$]"). iIntros "[Hlocked Hinv]".
    wp_pures.
    wp_apply (wp_forBreak_cond (λ continue,
                  "Hlocked" ∷ lock.locked #mu_l ∗
                  "Hinv" ∷ lock_inv l γ ∗
                  "HQ" ∷ if continue then recv γ Q else ▷ Q ∗ recv γ emp
                )%I with "[] [$Hlocked $Hinv $HrecvQ]").
    - clear Φ.
      iModIntro.
      wp_start as "H"; iNamed "H".
      iNamed "Hinv".
      wp_loadField; wp_pures.
      wp_if_destruct.
      + wp_pures. wp_loadField.
        wp_apply (wp_Cond__Wait with "[-HΦ HQ]").
        { iFrame "#∗". }
        iIntros "[Hlocked Hinv]".
        wp_pures. iModIntro. iApply "HΦ"; iFrame.
      + iMod (own_barrier_ghost_recv with "[$Hbar $HQ]") as "(Hbar & Hrecv & HQ)".
        { move: Heqb. word. }

        iModIntro.
        iApply "HΦ".
        rewrite /named.
        iFrame.
    - iIntros "H"; iNamed "H". iDestruct "HQ" as "[HQ Hrecv_emp]".
      wp_pures. wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hinv]").
      wp_pures.
      iModIntro. iApply "HΦ". iFrame.
  Qed.

End proof.

End barrier.

#[global] Typeclasses Opaque barrier.is_barrier barrier.send barrier.recv.
```
