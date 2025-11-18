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

From New.proof Require Import sync.
From New.generatedproof.sys_verif_code Require Import hashmap.
From Perennial.algebra Require Import ghost_var.

Module atomic_ptr.
Section proof.
  Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.
  Context `{!ghost_varG Σ loc}.

  Implicit Types (γ: gname).

  #[global] Instance : IsPkgInit hashmap := define_is_pkg_init True%I.
  #[global] Instance : GetIsPkgInitWf hashmap := build_get_is_pkg_init_wf.

  Definition own_ptr γ (x: loc) :=
    ghost_var γ (DfracOwn (1/2)) x.

  #[global] Instance own_ptr_timeless γ x : Timeless (own_ptr γ x).
  Proof. apply _. Qed.

  #[local] Definition lock_inv γ l : iProp _ :=
    ∃ (mref: loc),
      "val" ∷ l ↦s[hashmap.atomicPtr :: "val"] mref ∗
      "Hauth" ∷ ghost_var γ (DfracOwn (1/2)) mref.

  Definition is_atomic_ptr γ (l: loc) : iProp _ :=
    ∃ (mu_l: loc),
    "mu" ∷ l ↦s[hashmap.atomicPtr :: "mu"]□ mu_l ∗
    "Hlock" ∷ is_Mutex mu_l (lock_inv γ l).

  #[global] Instance is_atomic_ptr_persistent γ l : Persistent (is_atomic_ptr γ l).
  Proof. apply _. Qed.

  Lemma wp_newAtomicPtr (m_ref: loc) :
    {{{ is_pkg_init hashmap }}}
      @! hashmap.newAtomicPtr #m_ref
    {{{ γ (l: loc), RET #l; is_atomic_ptr γ l ∗ own_ptr γ m_ref }}}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_alloc mu_ptr as "mu".
    wp_auto.
    wp_alloc l as "Hptr".
    iApply struct_fields_split in "Hptr".
    iNamed "Hptr".
    cbn [hashmap.atomicPtr.mu' hashmap.atomicPtr.val'].
    iPersist "Hmu".
    iMod (ghost_var_alloc m_ref) as (γ) "[Hown Hauth]".
    iMod (init_Mutex (lock_inv γ l)
           with "mu [Hauth Hval]") as "Hlock".
    { iFrame. }
    wp_auto.
    wp_finish.
    iFrame "#∗".
  Qed.

  Lemma wp_atomicPtr__load γ l :
    ∀ (Φ: val → iProp Σ),
    (is_pkg_init hashmap ∗
    is_atomic_ptr γ l ∗
    |={⊤,∅}=> ∃ x, own_ptr γ x ∗ (own_ptr γ x ={∅,⊤}=∗ Φ #x)) -∗
    WP l @ (ptrT.id hashmap.atomicPtr.id) @ "load" #() {{ Φ }}.
  Proof.
    iIntros (Φ) "(#? & #Hint & Hau)".
    wp_method_call. wp_call.
    iNamed "Hint".
    wp_auto.

    wp_apply (wp_Mutex__Lock with "[$Hlock]").
    iIntros "[Hlocked Hinv]". iNamed "Hinv".
    wp_auto.

    iApply fupd_wp.
    iMod "Hau" as (x0) "[Hown Hclose]".
    iDestruct (ghost_var_agree with "Hauth Hown") as %Heq; subst x0.
    iMod ("Hclose" with "Hown") as "HΦ".
    iModIntro.

    wp_alloc map_val as "Hmap".
    wp_auto.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hauth val]").
    { iFrame. }

    iApply "HΦ".
  Qed.

  Lemma wp_atomicPtr__store γ l (y: loc) :
    ∀ Φ,
    (is_pkg_init hashmap ∗ is_atomic_ptr γ l ∗
    |={⊤,∅}=> ∃ x, own_ptr γ x ∗ (own_ptr γ y ={∅,⊤}=∗ Φ #())) -∗
    WP l @ (ptrT.id hashmap.atomicPtr.id) @ "store" #y {{ Φ }}.
  Proof.
    iIntros (Φ) "(#? & #Hint & Hau)".
    wp_method_call. wp_call.
    iNamed "Hint".
    wp_auto.

    wp_apply (wp_Mutex__Lock with "[$Hlock]").
    iIntros "[Hlocked Hinv]". iNamed "Hinv".
    wp_auto.

    iApply fupd_wp.
    iMod "Hau" as (x0) "[Hown Hclose]".
    iDestruct (ghost_var_agree with "Hauth Hown") as %Heq; subst x0.
    iMod (ghost_var_update_2 y with "Hauth Hown") as "[Hauth Hown]".
    { rewrite dfrac_op_own Qp.half_half //. }
    iMod ("Hclose" with "Hown") as "HΦ".
    iModIntro.

    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hauth val]").
    { iFrame. }

    iApply "HΦ".
  Qed.

End proof.

#[global] Typeclasses Opaque is_atomic_ptr.

End atomic_ptr.

Import atomic_ptr.

Section proof.
  Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.
  Context `{!ghost_varG Σ loc}.
  Context `{!ghost_varG Σ (gmap w64 w64)}.

  Let N := nroot .@ "hashmap".

  (* This hashmap implementation has an atomic pointer to a read-only copy of the
    map. Writes do a deep copy of the map to avoid disturbing reads.

    In the TaDA style, we use ghost variables to track the logical state:
    - γ_ptr: ghost variable tracking which map reference the atomic pointer holds
    - γ_map: ghost variable tracking the logical value of the map

    The internal invariant [hashmap_inv] relates the pointer's current mref
    (tracked by γ_ptr) to the actual map contents stored at that location.
    Half of γ_map is owned by the lock invariant (so writes can freeze the logical
    value), and half is given to the user via [own_hashmap].
   *)

  Definition own_hashmap γ (m: gmap w64 w64) :=
    ghost_var γ (DfracOwn (1/2)) m.

  #[global] Instance own_hashmap_timeless γ m : Timeless (own_hashmap γ m).
  Proof. apply _. Qed.

  Definition hashmap_inv γ γ_ptr : iProp _ :=
    ∃ (mref: loc) (m: gmap w64 w64),
    "Hptr" ∷ atomic_ptr.own_ptr γ_ptr mref ∗
    "#Hm_clean" ∷ own_map mref DfracDiscarded m ∗
    "Hm_var" ∷ ghost_var γ (DfracOwn (1/4)) m.

  Definition lock_inv (γ_map: gname): iProp _ :=
    ∃ (m: gmap w64 w64),
     "Hm_lock" ∷ ghost_var γ_map (DfracOwn (1/4)) m
  .

  Definition is_hashmap γ γ_ptr (l: loc) : iProp _ :=
    ∃ (ptr_l mu_l: loc),
    "#clean" ∷ l ↦s[hashmap.HashMap :: "clean"]□ ptr_l ∗
    "#mu" ∷ l ↦s[hashmap.HashMap :: "mu"]□ mu_l ∗
    "#Hclean" ∷ is_atomic_ptr γ_ptr ptr_l ∗
    "#Hlock" ∷ is_Mutex mu_l (lock_inv γ) ∗
    "#Hinv" ∷ inv N (hashmap_inv γ γ_ptr).

  #[global] Instance is_hashmap_persistent γ γ_ptr l : Persistent (is_hashmap γ γ_ptr l) := _.

  Lemma wp_NewHashMap :
    {{{ is_pkg_init hashmap }}}
      @! hashmap.NewHashMap #()
    {{{ γ γ_ptr (l: loc), RET #l; is_hashmap γ γ_ptr l ∗ own_hashmap γ ∅ }}}.
  Proof.
    wp_start as "_".
    wp_auto.
    wp_apply (wp_map_make (K:=w64) (V:=w64)) as "%mref Hm".
    { reflexivity. }
    iPersist "Hm".
    iMod (ghost_var_alloc (∅: gmap w64 w64)) as (γ) "[[Hm_inv Hm_lock_inv] Hm_user]".
    wp_apply (wp_newAtomicPtr mref).
    iIntros (γ_ptr ptr_l) "[Hptr Hown_ptr]".
    wp_auto.
    wp_alloc mu_l as "Hmu".
    wp_auto.
    replace (1/2/2)%Qp with (1/4)%Qp by compute_done.
    iMod (init_Mutex (lock_inv γ) with "Hmu [$Hm_lock_inv]") as "Hlock".
    iMod (inv_alloc N _ (hashmap_inv γ γ_ptr) with "[Hown_ptr Hm_inv]") as "#Hinv".
    { iModIntro. iFrame "∗#". }
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

  (* FIXME: eventually use upstream perennial instance *)
  #[global] Instance own_map_timeless
  `{!IntoVal K} `{!EqDecision K} `{!Countable K} `{!IntoVal V}
    mptr dq (m: gmap K V)
  `{!IntoValTyped K kt} `{!IntoValTyped V vt}
    : Timeless (own_map mptr dq m).
  Proof. rewrite own_map_unseal. apply _. Qed.

  Lemma wp_HashMap__Load γ γ_ptr l (key: w64) :
    ∀ (Φ: val → iProp Σ),
    (is_pkg_init hashmap ∗
    is_hashmap γ γ_ptr l ∗
    |={⊤∖↑N,∅}=> ∃ m, own_hashmap γ m ∗ (own_hashmap γ m ={∅,⊤∖↑N}=∗ Φ (#(fst (map_get (m !! key))), #(snd (map_get (m !! key))))%V)) -∗
    WP l @ (ptrT.id hashmap.HashMap.id) @ "Load" #key {{ Φ }}.
  Proof.
    iIntros (Φ) "(#? & #Hmap & Hau)".
    wp_method_call. wp_call.
    iNamed "Hmap".
    wp_auto.
    wp_alloc clean_m_ptr as "Hnew_clean".
    wp_auto.

    wp_apply (wp_atomicPtr__load). iFrame "Hclean".
    (* Now we prove the atomic update of the load. The linearization point of
    loading this pointer is _also_ the linearization point for the hashmap
    load, so we need to both open our invariant (to get temporary ownership of
    the pointer) and fire the user's AU while we have a chance. *)
    iInv "Hinv" as ">HI" "Hclose".
    iMod "Hau" as (m) "[Hm Hau]".
    iNamedSuffix "HI" "_inv".
    iModIntro.
    iFrame "Hptr_inv". iIntros "Hptr_inv".
    (* this is the crucial information we learn from opening the invariant
    (other than this, we open and close it as-is, since this operation is
    read-only) *)
    iDestruct (ghost_var_agree with "Hm_var_inv Hm") as %<-.
    iMod ("Hau" with "Hm") as "HΦ".

    (* Close the hashmap invariant *)
    iMod ("Hclose" with "[$Hptr_inv $Hm_var_inv]").
    { iModIntro. iFrame "∗#". }

    iModIntro.
    wp_auto.
    wp_apply (wp_map_get with "[$]").
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
  Lemma wp_HashMap__dirty (γ γ_ptr: gname) l (ptr_l: loc) (m: gmap w64 w64) :
    {{{ is_pkg_init hashmap ∗
        "#clean" ∷ l ↦s[hashmap.HashMap :: "clean"]□ ptr_l ∗
        "#Hclean" ∷ is_atomic_ptr γ_ptr ptr_l ∗
        "#Hinv" ∷ inv N (hashmap_inv γ γ_ptr) ∗
        "Hm_lock" ∷ ghost_var γ (DfracOwn (1/4)) m }}}
      l @ (ptrT.id hashmap.HashMap.id) @ "dirty" #()
    {{{ (mref: loc), RET #mref;
      own_map (kt:=uint64T) mref (DfracOwn 1) m ∗
      ghost_var γ (DfracOwn (1/4)) m }}}.
  Proof.
    wp_start as "Hpre". iNamed "Hpre".
    wp_auto.
    wp_alloc new_clean_ptr as "Hnew_clean".
    wp_auto.

    wp_apply (wp_atomicPtr__load). iFrame "Hclean".
    (* Open hashmap invariant to get pointer ownership *)
    iInv "Hinv" as ">HI" "Hclose_inv".
    iApply fupd_mask_intro; [ set_solver | iIntros "Hmask" ].
    iNamedSuffix "HI" "_inv".

    (* Give pointer ownership to atomic_ptr *)
    iFrame "Hptr_inv". iIntros "Hptr_inv".

    (* Obtain that the map values agree *)
    iMod "Hmask" as "_".
    iDestruct (ghost_var_agree with "Hm_var_inv Hm_lock") as %<-.

    (* Close the invariant *)
    iMod ("Hclose_inv" with "[Hptr_inv Hm_var_inv]").
    { iModIntro. iFrame "∗#". }

    iModIntro.
    wp_auto.
    wp_apply (wp_mapClone with "[$]").
    iIntros (mref') "Hdirty".
    wp_auto.
    wp_finish.
  Qed.

  Lemma wp_HashMap__Store γ γ_ptr l (key: w64) (val: w64) :
    ∀ Φ,
    (is_pkg_init hashmap ∗
    is_hashmap γ γ_ptr l ∗
    |={⊤ ∖ ↑N,∅}=> ∃ m, own_hashmap γ m ∗
        (own_hashmap γ (map_insert key val m) ={∅,⊤ ∖ ↑N}=∗ Φ #())) -∗
    WP l @ (ptrT.id hashmap.HashMap.id) @ "Store" #key #val {{ Φ }}.
  Proof.
    iIntros (Φ) "(#? & #Hmap & Hau)".
    wp_method_call. wp_call.
    iNamed "Hmap".
    wp_auto.
    wp_apply (wp_Mutex__Lock with "[$Hlock]"). iIntros "[Hlocked Hlock_inv]".
    iNamed "Hlock_inv".
    wp_auto.
    wp_apply (wp_HashMap__dirty with "[$clean $Hclean $Hinv $Hm_lock]").
    iIntros (mref) "[Hdirty Hm_lock]".
    wp_auto.
    wp_apply (wp_map_insert with "Hdirty").
    iIntros "Hm".
    iPersist "Hm" as "Hm_new".
    wp_auto.

    wp_apply (wp_atomicPtr__store). iFrame "Hclean".
    (* Open hashmap invariant *)
    iInv "Hinv" as ">HI" "Hclose_inv".
    iMod "Hau" as (m0) "[Hown Hclose_au]".
    iNamedSuffix "HI" "_inv".
    iModIntro.

    (* Give old pointer ownership, get new pointer ownership *)
    iFrame "Hptr_inv". iIntros "Hptr_inv".

    (* Update ghost variables and execute user's AU *)
    iDestruct (ghost_var_agree with "Hm_var_inv Hm_lock") as %<-.
    iDestruct (ghost_var_agree with "Hm_var_inv Hown") as %<-.
    iCombine "Hm_lock Hm_var_inv" as "Hm1".
    rewrite Qp.quarter_quarter.
    iMod (ghost_var_update_2 (<[key:=val]> m1) with "Hm1 Hown") as "[Hm1 Hown]".
    { rewrite dfrac_op_own Qp.half_half //. }
    iDestruct "Hm1" as "[Hm_lock Hm_var_inv]".
    iMod ("Hclose_au" with "Hown") as "HΦ".
    replace (1/2/2)%Qp with (1/4)%Qp by compute_done.

    (* Close invariant with new map value *)
    iMod ("Hclose_inv" with "[Hptr_inv Hm_var_inv]").
    { iModIntro. iFrame "∗#". }

    iModIntro.
    wp_auto.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hm_lock]").
    { iFrame. }
    wp_finish.
  Qed.

  Lemma wp_HashMap__Delete γ γ_ptr l (key: w64) :
    ∀ Φ,
    (is_pkg_init hashmap ∗
    is_hashmap γ γ_ptr l ∗
    |={⊤ ∖ ↑N,∅}=> ∃ m, own_hashmap γ m ∗
        (own_hashmap γ (delete key m) ={∅,⊤ ∖ ↑N}=∗ Φ #())) -∗
    WP l @ (ptrT.id hashmap.HashMap.id) @ "Delete" #key {{ Φ }}.
  Proof.
    (* notice how this proof is nearly identical to that for Store: the way this
    code works generally achieves atomicity for any critical section *)
    iIntros (Φ) "(#? & #Hmap & Hau)".
    wp_method_call. wp_call.
    iNamed "Hmap".
    wp_auto.
    wp_apply (wp_Mutex__Lock with "[$Hlock]"). iIntros "[Hlocked Hlock_inv]".
    iNamed "Hlock_inv".
    wp_auto.
    wp_apply (wp_HashMap__dirty with "[$clean $Hclean $Hinv $Hm_lock]").
    iIntros (mref) "[Hdirty Hm_lock]".
    wp_auto.
    wp_apply (wp_map_delete with "Hdirty").
    iIntros "Hm".
    iPersist "Hm" as "Hm_new".
    wp_auto.

    wp_apply (wp_atomicPtr__store). iFrame "Hclean".
    (* Open hashmap invariant *)
    iInv "Hinv" as ">HI" "Hclose_inv".
    iMod "Hau" as (m0) "[Hown Hclose_au]".
    iNamedSuffix "HI" "_inv".
    iModIntro.

    (* Give old pointer ownership, get new pointer ownership *)
    iFrame "Hptr_inv". iIntros "Hptr_inv".

    (* Update ghost variables and execute user's AU *)
    iDestruct (ghost_var_agree with "Hm_var_inv Hm_lock") as %<-.
    iDestruct (ghost_var_agree with "Hm_var_inv Hown") as %<-.
    iCombine "Hm_lock Hm_var_inv" as "Hm1".
    rewrite Qp.quarter_quarter.
    iMod (ghost_var_update_2 (delete key m1) with "Hm1 Hown") as "[Hm1 Hown]".
    { rewrite dfrac_op_own Qp.half_half //. }
    iDestruct "Hm1" as "[Hm_lock Hm_var_inv]".
    iMod ("Hclose_au" with "Hown") as "HΦ".
    replace (1/2/2)%Qp with (1/4)%Qp by compute_done.

    (* Close invariant with new map value *)
    iMod ("Hclose_inv" with "[Hptr_inv Hm_var_inv]").
    { iModIntro. iFrame "∗#". }

    iModIntro.
    wp_auto.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hm_lock]").
    { iFrame. }
    wp_finish.
  Qed.

End proof.

#[global] Typeclasses Opaque is_hashmap.
```
