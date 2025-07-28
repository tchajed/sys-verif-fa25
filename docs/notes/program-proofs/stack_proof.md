---
# Auto-generated from literate source. DO NOT EDIT.
category: demo
tags: literate
order: -1
pageInfo: ["Date", "Category", "Tag"]
shortTitle: "Demo: stack"
---

# Demo: stack data structure

This is a stack used to implement a queue (using two stacks).

---

```rocq
From sys_verif.program_proof Require Import prelude empty_ffi.
From sys_verif.program_proof Require Import heap_init.

Section proof.
Context `{hG: !heapGS Σ} `{!goGlobalsGS Σ}.

```

The stack representation invariant has one interesting detail: when we "push" to the stack it will go from `stack_rep l xs` to `stack_rep l (cons x xs)`, even though the code appends. This is allowed; it just requires that the logical elements of the stack are the reverse of the physical elements of the slice.

Understanding this is not needed to use these specifications (by design, you do not need to read the definition of `stack_rep` to understand how to use it). However, for the purposes of the class it's important you understand the difference between the physical state and the abstract representation and why it's okay to have this `reverse` here.

```rocq
Definition stack_rep (l: loc) (xs: list w64): iProp Σ :=
  ∃ (s: slice.t),
    "elements" ∷ l ↦s[heap.Stack :: "elements"] s ∗
    (* The code appends because this is both easier and more efficient, thus the
    code elements are reversed compared to the abstract state. *)
    "Hels" ∷ own_slice s (DfracOwn 1) (reverse xs) ∗
    "Hels_cap" ∷ own_slice_cap w64 s.

Lemma wp_NewStack :
  {{{ is_pkg_init heap.heap }}}
    heap.heap @ "NewStack" #()
  {{{ l, RET #l; stack_rep l [] }}}.
Proof.
  wp_start as "_".
  wp_alloc l as "H".
  wp_auto.
  iApply struct_fields_split in "H". iNamed "H". cbn [heap.Stack.elements'].
  iApply "HΦ".
  iFrame.
  iSplitL.
  - iApply own_slice_nil.
  - iApply own_slice_cap_nil.
Qed.

Lemma wp_Stack__Push l xs (x: w64) :
  {{{ is_pkg_init heap.heap ∗ stack_rep l xs }}}
    l @ heap.heap @ "Stack'ptr" @ "Push" #x
  {{{ RET #(); stack_rep l (x :: xs) }}}.
Proof.
  wp_start as "Hstack".
  iNamed "Hstack".
  wp_auto.
  wp_apply (wp_slice_literal) as "%s_tmp Hs_tmp".
  wp_apply (wp_slice_append with "[$Hels $Hels_cap $Hs_tmp]").
  iIntros (s') "(Hels & Hels_cap & Hs_tmp)".
  wp_auto.
  iApply "HΦ".
  iFrame "elements Hels_cap".
  rewrite reverse_cons.
  iFrame.
Qed.

(* It's convenient to factor out the spec for stack a bit, to deal with the way
Go handles returning failure (the boolean in Pop's return value). *)
Definition stack_pop (xs: list w64) : w64 * bool * list w64 :=
  match xs with
  | [] => (W64 0, false, [])
  | x :: xs => (x, true, xs)
  end.

Lemma stack_pop_rev (xs: list w64) :
  (xs = [] ∧ stack_pop (reverse xs) = (W64 0, false, [])) ∨
  (∃ x xs', xs = xs' ++ [x] ∧ stack_pop (reverse xs) = (x, true, reverse xs')).
Proof.
  induction xs using rev_ind.
  - simpl. left. auto.
  - right. exists x, xs.
    split; [ done | ].
    rewrite reverse_app //=.
Qed.

Hint Rewrite @length_reverse : len.

Lemma wp_Stack__Pop l xs :
  {{{ is_pkg_init heap.heap ∗ stack_rep l xs }}}
    l @ heap.heap @ "Stack'ptr" @ "Pop" #()
  {{{ (x: w64) (ok: bool) xs', RET (#x, #ok);
      stack_rep l xs' ∗
      ⌜(x, ok, xs') = stack_pop xs⌝
  }}}.
Proof.
  wp_start as "Hstack". iNamed "Hstack".
  wp_auto.
  iDestruct (own_slice_len with "Hels") as %Hlen.
  wp_if_destruct.
  {
    iApply "HΦ".
    iFrame.
    iPureIntro.
    rewrite /stack_pop.
    assert (xs = []).
    { destruct xs; auto.
      autorewrite with len in Hlen.
      word.
    }
    subst. auto.
  }
  wp_auto.
  assert (0 < length xs).
  { rewrite length_reverse in Hlen. word. }
  wp_pure.
  { word. }
  list_elem (reverse xs) (uint.nat (slice.len_f s) - 1)%nat as x_last.
  { word. }
  wp_apply (wp_load_slice_elem with "[$Hels]").
  { replace (uint.nat (word.sub (slice.len_f s) (W64 1))) with (uint.nat (slice.len_f s) - 1)%nat by word.
    eauto. }
  iIntros "Hels".
  wp_auto.
  iDestruct (own_slice_wf with "Hels") as %Hcap.
  (* TODO: need wp for slice.slice *)
  (*
  wp_apply (wp_SliceTake_full with "Hels").
  { word. }
  iIntros "Hels".
  wp_storeField.
  wp_pures.
  iModIntro. iApply "HΦ".
  rewrite /stack_rep.
  iFrame "elements".
  iSplit.
  {
    replace (uint.nat (word.sub (Slice.sz s) (W64 1))) with
      (uint.nat (Slice.sz s) - 1)%nat by word.
    rewrite take_reverse. rewrite length_reverse in Hlen.
    replace (length xs - (uint.nat (Slice.sz s) - 1))%nat with 1%nat by word.
    iFrame.
  }
  iPureIntro.
  rewrite /stack_pop.
  destruct xs; auto.
  - exfalso. simpl in *; lia.
  - simpl. rewrite drop_0.
    f_equal.
    f_equal.
    apply reverse_lookup_Some in Hx_last_lookup as [Hget ?].
    rewrite length_reverse in Hlen.
    simpl in Hget, Hlen.
    replace (length xs - (uint.nat (Slice.sz s) - 1))%nat with 0%nat
      in Hget by lia.
    simpl in Hget.
    congruence.
*)
Admitted.

End proof.
```
