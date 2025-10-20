---
# Auto-generated from literate source. DO NOT EDIT.
category: demo
shortTitle: "Demo: Goose basics"
tags: literate
date: 2025-10-16 8:00:00 -5
pageInfo: ["Date", "Category", "Tag"]
---

# Demo: proofs of functional Go code

Here are some proofs of "functional" Go code that just does some arithmetic and doesn't interact with the heap.

```rocq
From sys_verif.program_proof Require Import prelude.

From New.golang.theory Require Import pkg.
From New.proof Require Import std.
From sys_verif.program_proof Require Import functional_init.

Section proof.
  Context `{hG: heapGS Σ, !ffi_semantics _ _}.
  Context `{!globalsGS Σ} {go_ctx: GoContext}.

  (** Even the simple Add function has one subtlety: integer overflow. We prove
  a spec for it that assumes there is no overflow. *)
  Lemma wp_Add (a b: w64) :
    {{{ is_pkg_init functional ∗ ⌜uint.Z a + uint.Z b < 2^64⌝ }}}
      @! functional.Add #a #b
    {{{ (c: w64), RET #c; ⌜uint.Z c = (uint.Z a + uint.Z b)%Z⌝  }}}.
  Proof.
    wp_start as "%Hoverflow".
    wp_alloc b_l as "b"; wp_pures.
    wp_alloc a_l as "a"; wp_pures.
    wp_load; wp_load; wp_pures.
    iApply "HΦ".
    iPureIntro.
    word.
  Qed.

  Lemma wp_Add_general (a b: w64) :
    {{{ is_pkg_init functional }}}
      @! functional.Add #a #b
    {{{ RET #(word.add a b); True }}}.
  Proof.
    wp_start.
    wp_auto.
    iApply "HΦ"; done.
  Qed.

  Lemma wp_Max (a b: w64) :
    {{{ is_pkg_init functional }}}
      @! functional.Max #a #b
    {{{ (c: w64), RET #c; ⌜uint.Z a ≤ uint.Z c ∧ uint.Z b ≤ uint.Z c⌝  }}}.
  Proof.
    wp_start.
    wp_auto.
    wp_if_destruct.
    - iApply "HΦ".
      word.
    - iApply "HΦ".
      word.
  Qed.

  Lemma wp_Midpoint (a b: w64) :
    {{{ is_pkg_init functional ∗ ⌜uint.Z a + uint.Z b < 2^64⌝ }}}
      @! functional.Midpoint #a #b
    {{{ (c: w64), RET #c; ⌜uint.Z c = (uint.Z a + uint.Z b) / 2⌝ }}}.
  Proof.
    wp_start as "%Hoverflow".
    wp_auto.
    iApply "HΦ".
    word.
  Qed.

  Lemma wp_Midpoint2 (a b: w64) :
    {{{ is_pkg_init functional }}}
      @! functional.Midpoint2 #a #b
    {{{ (c: w64), RET #c; ⌜uint.Z c = (uint.Z a + uint.Z b) / 2⌝ }}}.
  Proof.
    wp_start.
    wp_auto.
    wp_if_destruct.
    - iApply "HΦ".
      word.
    - iApply "HΦ".
      word.
  Qed.

  Lemma wp_Arith (a b: w64) :
    {{{ is_pkg_init functional }}}
      @! functional.Arith #a #b
    {{{ (c: w64), RET #c; True }}}.
  Proof.
    wp_start.
    wp_auto.
    wp_if_destruct.
    - iApply "HΦ".
      done.
    - wp_apply wp_Midpoint2.
      iIntros "%c %Heq".
      wp_auto.
      iApply "HΦ".
      done.
  Qed.

End proof.
```
