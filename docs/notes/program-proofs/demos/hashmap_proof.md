---
# Auto-generated from literate source. DO NOT EDIT.
category: demo
tags: literate
order: 10
shortTitle: "Demo: hashmap proof"
---

# Demo: verifying a concurrent hashmap

> The Rocq code for this file is at [src/sys_verif/program_proof/demos/hashmap_proof.v](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/src/sys_verif/program_proof/demos/hashmap_proof.v).

```rocq
From sys_verif.program_proof Require Import prelude empty_ffi.

From iris.base_logic.lib Require Import ghost_var.
From New.proof Require Import sync.
From New.generatedproof.sys_verif_code Require Import hashmap.

Module atomic_ptr.
Section proof.
  Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.

  #[global] Instance : IsPkgInit hashmap := define_is_pkg_init True%I.
  #[global] Instance : GetIsPkgInitWf hashmap := build_get_is_pkg_init_wf.

  #[local] Definition lock_inv l (P: loc → iProp Σ): iProp _ :=
    ∃ (mref: loc), "val" ∷ l ↦s[hashmap.atomicPtr :: "val"] mref ∗
       "HP" ∷ P mref.

  Definition is_atomic_ptr (l: loc) (P: loc → iProp Σ): iProp _ :=
    ∃ (mu_l: loc),
    "mu" ∷ l ↦s[hashmap.atomicPtr :: "mu"]□ mu_l ∗
    "Hlock" ∷ is_Mutex mu_l (lock_inv l P).

  #[global] Instance is_atomic_ptr_persistent l P : Persistent (is_atomic_ptr l P).
  Proof. apply _. Qed.

  Lemma wp_newAtomicPtr (P: loc → iProp Σ) (m_ref: loc) :
    {{{ is_pkg_init hashmap ∗ P m_ref }}}
      @! hashmap.newAtomicPtr #m_ref
    {{{ (l: loc), RET #l; is_atomic_ptr l P }}}.
  Proof.
    wp_start as "HP".
    wp_auto.
    wp_alloc mu_ptr as "mu".
    wp_auto.
    wp_alloc l as "Hptr".
    iApply struct_fields_split in "Hptr".
    iNamed "Hptr".
    cbn [hashmap.atomicPtr.mu' hashmap.atomicPtr.val'].
    iPersist "Hmu".
    iMod (init_Mutex (lock_inv l P)
           with "mu [HP Hval]") as "Hlock".
    { iFrame. }
    wp_auto.
    wp_finish.
    iFrame "#∗".
  Qed.

  Lemma wp_atomicPtr__load l (P: loc → iProp _) (Q: loc → iProp Σ) :
    {{{ is_pkg_init hashmap ∗
          is_atomic_ptr l P ∗ (∀ x, P x -∗ |={⊤}=> Q x ∗ P x) }}}
      l @ (ptrT.id hashmap.atomicPtr.id) @ "load" #()
    {{{ (x: loc), RET #x; Q x }}}.
  Proof.
    wp_start as "[#Hint Hfupd]".
    iNamed "Hint".
    wp_auto.
    wp_apply (wp_Mutex__Lock with "[$Hlock]").
    iIntros "[Hlocked Hinv]". iNamed "Hinv".
    wp_auto.
    iMod ("Hfupd" with "HP") as "[HQ HP]".
    wp_alloc map_val as "Hmap".
    wp_auto.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked HP val]").
    { iFrame. }

    wp_finish.
  Qed.

  Lemma wp_atomicPtr__store l (P: loc → iProp _) (Q: loc → iProp _) (y: loc) :
    {{{ is_pkg_init hashmap ∗ is_atomic_ptr l P ∗
          (∀ x, P x -∗ |={⊤}=> Q x ∗ P y) }}}
      l @ (ptrT.id hashmap.atomicPtr.id) @ "store" #y
    {{{ (x: loc), RET #(); Q x }}}.
  Proof.
    wp_start as "[#Hint Hfupd]".
    iNamed "Hint".
    wp_auto.
    wp_apply (wp_Mutex__Lock with "[$Hlock]").
    iIntros "[Hlocked Hinv]". iNamed "Hinv".
    wp_auto.

    iMod ("Hfupd" with "HP") as "[HQ HP]".

    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked HP val]").
    { iFrame. }

    wp_finish.
  Qed.

End proof.

#[global] Typeclasses Opaque is_atomic_ptr.

End atomic_ptr.

Import atomic_ptr.

Section proof.
  Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.
  Context `{!ghost_varG Σ (gmap w64 w64)}.

  Definition ptr_rep (γ: gname) (P: gmap w64 w64 → iProp _) (mref: loc): iProp _ :=
      ∃ (m: gmap w64 w64),
      "#Hm_clean" ∷ own_map mref DfracDiscarded m ∗
      "HP" ∷ P m ∗
      "Hm_var" ∷ ghost_var γ (1/2) m
      .

  Definition lock_inv (γ: gname): iProp _ :=
    ∃ (m: gmap w64 w64),
     "Hm_lock" ∷ ghost_var γ (1/2) m
     .

  (* Recall that the [P] argument is a representation invariant from the user of
     the hashmap, which we need to maintain. Intuitively, [P m] should always hold
     for some [m] that is the logically current state of the hashmap.

    This hashmap implementation has an atomic pointer to a read-only copy of the
    map. Writes do a deep copy of the map to avoid disturbing reads.

    The know from the state that the invariant for the hashmap consists of two
    pieces: the representation predicate for the atomic pointer, and the lock
    invariant. It turns out these two are enough (and we won't need a separate
    invariant). Notice that we have the _caller_'s representation predicate [P]
    for the actual map value, as well as the internal _hashmap_ predicate
    [ptr_rep] for the map reference itself. We can guess that [ptr_rep] must
    contain the caller's [P], since reads don't use the lock and yet still must
    read the current value of the map.

    For writes, each operation gets the current value of the map, does a deep
    copy (to allow modifications), and then stores the new map. We need a lock
    to prevent a concurrent write from overlapping (think about how a write
    could be lost if we didn't). So, the lock invariant captures that the
    logical value of the map is frozen while the lock is held. We implement that
    in Iris with a ghost variable whose value is the current map value - in
    addition to maintaining [P m], we'll also have [ghost_var γ q m]. That ghost
    variable will be half owned by the atomic pointer (since it needs to match
    the physical state), and half owned by the _lock invariant_. This means upon
    acquiring the lock the write operation knows the current value of the map
    can no longer change, while still allowing reads.
   *)

  Definition is_hashmap (l: loc) (P: gmap w64 w64 → iProp _): iProp _ :=
    ∃ (ptr_l mu_l: loc) γ,
    "#clean" ∷ l ↦s[hashmap.HashMap :: "clean"]□ ptr_l ∗
    "#mu" ∷ l ↦s[hashmap.HashMap :: "mu"]□ mu_l ∗
    "#Hclean" ∷ is_atomic_ptr ptr_l (ptr_rep γ P) ∗
    "#Hlock" ∷ is_Mutex mu_l (lock_inv γ)
    .

  #[global] Instance is_hashmap_persistent l P : Persistent (is_hashmap l P) := _.

  Lemma wp_NewHashMap (P: gmap w64 w64 → iProp _) :
    {{{ is_pkg_init hashmap ∗ P ∅ }}}
      @! hashmap.NewHashMap #()
    {{{ (l: loc), RET #l; is_hashmap l P }}}.
  Proof.
    wp_start as "HP".
    wp_auto.
    wp_apply (wp_map_make (K:=w64) (V:=w64)) as "%mref Hm".
    { reflexivity. }
    iPersist "Hm".
    iMod (ghost_var_alloc (∅: gmap w64 w64)) as (γ) "[Hm_var Hm_lock]".
    wp_apply (wp_newAtomicPtr (ptr_rep γ P) with "[Hm_var $HP]").
    { iFrame "∗#". }
    iIntros (ptr_l) "Hptr".
    wp_auto.
    wp_alloc mu_l as "Hmu".
    wp_auto.
    iMod (init_Mutex (lock_inv γ) with "Hmu [$Hm_lock]") as "Hlock".
    wp_alloc l as "Hmap".
    iApply struct_fields_split in "Hmap". iNamed "Hmap".
    cbn [hashmap.HashMap.clean' hashmap.HashMap.mu'].
    iPersist "Hclean Hmu".
    wp_auto.
    wp_finish.
    iFrame "∗#".
  Qed.

  Lemma wp_mapClone mref (m: gmap w64 w64) :
    {{{ is_pkg_init hashmap ∗ own_map (kt:=uint64T) mref DfracDiscarded m }}}
      @! hashmap.mapClone #mref
    {{{ (mref': loc), RET #mref';
      own_map (kt:=uint64T) mref' (DfracOwn 1) m }}}.
  Proof.
    wp_start as "#Hm".
    wp_auto.
    wp_apply (wp_map_make (K:=w64) (V:=w64)) as "%mref' Hm_new".
    { reflexivity. }
    (* TODO: need wp for map.for_range *)
    (*
    wp_apply (wp_MapIter_2 (K:=w64) (V:=w64) _ _ _ _ _ (λ mtodo mdone,
      own_map mref' (DfracOwn 1) mdone
    )%I with "[$Hm] [$Hm_new]").
    { clear Φ.
      iIntros (k v mtodo mdone).
      iIntros "!>" (Φ) "Hpre HΦ".
      iDestruct "Hpre" as "[Hm_new %Hget]".
      wp_apply (wp_MapInsert w64 w64 v with "[$Hm_new]").
      { eauto. }
      wp_auto.
      iIntros "Hm_new".
      wp_finish.
      rewrite /typed_map.map_insert.
      iFrame. }

    iIntros "[_ Hm_new]".
    wp_auto.
    wp_finish.
*)
  Admitted.

  Definition map_get `{!IntoVal V} `{!IntoValTyped V t} (v: option V) : V * bool :=
    (default (default_val V) v, bool_decide (is_Some v)).

  Lemma wp_HashMap__Load l (key: w64) (P: gmap w64 w64 → iProp _)
    (Q: (w64 * bool) → iProp _) :
  {{{ is_pkg_init hashmap ∗
        is_hashmap l P ∗ (∀ m, P m ={⊤}=∗ Q (map_get (m !! key)) ∗ P m) }}}
    l @ (ptrT.id hashmap.HashMap.id) @ "Load" #key
  {{{ (v: w64) (ok: bool), RET (#v, #ok); Q (v, ok) }}}.
  Proof.
    wp_start as "[#Hmap Hfupd]". iNamed "Hmap".
    wp_auto.
    wp_alloc clean_m_ptr as "Hnew_clean".
    wp_auto.
    wp_apply (wp_atomicPtr__load _ _ (λ mref,
      ∃ m, own_map mref DfracDiscarded m ∗
      Q (map_get (m !! key))
    )%I with "[$Hclean Hfupd]").

    { iIntros (mref) "Hrep". iNamed "Hrep".
      iMod ("Hfupd" with "HP") as "[HQ HP]".
      iModIntro.
      iFrame "#∗". }

    iIntros (mref) "(%m & #Hclean_map & HQ)".
    wp_auto.
    wp_apply (wp_map_get with "[$Hclean_map]").
    iIntros "_".
    wp_auto.
    wp_finish.
  Qed.

  (* The spec of this helper is a bit complicated since it is called with the
  lock held, hence a decent amount of context has to be passed in the
  precondition. The important part of the spec is that [m] is the current
  abstract state due to the [ghost_var] premise, and it is exactly the map
  returned as physical state. We can also see the spec returns [own_map] with a
  fraction of [1] due to the deep copy here. *)
  Lemma wp_HashMap__dirty (γ: gname) l (ptr_l: loc) (P: gmap w64 w64 → iProp _) (m: gmap w64 w64) :
    {{{ is_pkg_init hashmap ∗
        "#clean" ∷ l ↦s[hashmap.HashMap :: "clean"]□ ptr_l ∗
        "#Hclean" ∷ is_atomic_ptr ptr_l (ptr_rep γ P) ∗
        "Hm_lock" ∷ ghost_var γ (1/2) m }}}
      l @ (ptrT.id hashmap.HashMap.id) @ "dirty" #()
    {{{ (mref: loc), RET #mref;
      own_map (kt:=uint64T) mref (DfracOwn 1) m ∗
      ghost_var γ (1/2) m }}}.
  Proof.
    wp_start as "Hpre". iNamed "Hpre".
    wp_auto.
    wp_alloc new_clean_ptr as "Hnew_clean".
    wp_auto.
    wp_apply (wp_atomicPtr__load _ _ (λ mref,
      (* the important part is that this [m] matches the one in the precondition, because of the ghost variable *)
     own_map (kt:=uint64T) mref DfracDiscarded m ∗ ghost_var γ (1/2) m)%I
     with "[$Hclean Hm_lock]").
    { iIntros (mref) "Hrep". iNamed "Hrep".
      iDestruct (ghost_var_agree with "Hm_lock Hm_var") as %<-.
      iModIntro. iFrame "#∗". }
      iIntros (mref) "(Hclean_m & Hm)".
      wp_auto.
      wp_apply (wp_mapClone with "[$Hclean_m]").
      iIntros (mref') "Hdirty".
      wp_auto.
      wp_finish.
  Qed.

  Lemma wp_HashMap__Store l (key: w64) (val: w64) (P: gmap w64 w64 → iProp _)
    (Q: gmap w64 w64 → iProp _) :
  {{{ is_pkg_init hashmap ∗
      is_hashmap l P ∗
      (∀ m, P m ={⊤}=∗ Q m ∗ P (map_insert key val m)) }}}
    l @ (ptrT.id hashmap.HashMap.id) @ "Store" #key #val
  {{{ m, RET #(); Q m }}}.
  Proof.
    wp_start as "[#Hmap Hfupd]".
    iNamed "Hmap".
    wp_auto.
    wp_apply (wp_Mutex__Lock with "[$Hlock]"). iIntros "[Hlocked Hinv]".
    iNamed "Hinv".
    wp_auto.
    wp_apply (wp_HashMap__dirty with "[$clean $Hclean $Hm_lock]").
    iIntros (mref) "[Hdirty Hm_lock]".
    wp_auto.
    wp_apply (wp_map_insert with "Hdirty").
    iIntros "Hm".
    iPersist "Hm" as "Hm_new".
    wp_auto.
    wp_apply (wp_atomicPtr__store _ _
      (λ _, Q m ∗ ghost_var γ (1/2) (map_insert key val m))%I
     with "[$Hclean Hfupd Hm_lock]").
    { iIntros (mref') "Hrep". iNamed "Hrep".
      iDestruct (ghost_var_agree with "Hm_lock Hm_var") as %<-.
      iMod (ghost_var_update_halves (map_insert key val m) with "Hm_lock Hm_var") as "[Hm_lock Hm_var]".
      iMod ("Hfupd" with "HP") as "[HQ HP]".
      iModIntro.
      iFrame "∗#". }
    iIntros (_) "[HQ Hm_lock]".
    wp_auto.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hm_lock]").
    { iFrame. }
    wp_finish.
  Qed.

  Lemma wp_HashMap__Delete l (key: w64) (P: gmap w64 w64 → iProp _)
    (Q: gmap w64 w64 → iProp _) :
  {{{ is_pkg_init hashmap ∗
      is_hashmap l P ∗
      (∀ m, P m ={⊤}=∗ Q m ∗ P (delete key m)) }}}
    l @ (ptrT.id hashmap.HashMap.id) @ "Delete" #key
  {{{ m, RET #(); Q m }}}.
  Proof.
    wp_start as "[#Hmap Hfupd]".
    iNamed "Hmap".
    wp_auto.
    wp_apply (wp_Mutex__Lock with "[$Hlock]"). iIntros "[Hlocked Hinv]".
    iNamed "Hinv".
    wp_auto.
    wp_apply (wp_HashMap__dirty with "[$clean $Hclean $Hm_lock]").
    iIntros (mref) "[Hdirty Hm_lock]".
    wp_auto.
    wp_apply (wp_map_delete with "Hdirty").
    iIntros "Hm".
    iPersist "Hm" as "Hm_new".
    wp_auto.
    wp_apply (wp_atomicPtr__store _ _
      (λ _, Q m ∗ ghost_var γ (1/2) (delete key m))%I
     with "[$Hclean Hfupd Hm_lock]").
    { iIntros (mref') "Hrep". iNamed "Hrep".
      iDestruct (ghost_var_agree with "Hm_lock Hm_var") as %<-.
      iMod (ghost_var_update_halves (map_delete key m) with "Hm_lock Hm_var") as "[Hm_lock Hm_var]".
      iMod ("Hfupd" with "HP") as "[HQ HP]".
      iModIntro.
      iFrame "∗#". }
    iIntros (_) "[HQ Hm_lock]".
    wp_auto.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hm_lock]").
    { iFrame. }
    wp_finish.
  Qed.

End proof.

#[global] Typeclasses Opaque is_hashmap.
```
