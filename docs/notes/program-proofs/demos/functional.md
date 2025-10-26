---
# Auto-generated from literate source. DO NOT EDIT.
category: demo
shortTitle: "Demo: Goose basics"
order: 1
tags: literate
date: 2025-10-16 8:00:00 -5
pageInfo: ["Date", "Category", "Tag"]
---

# Demo: proofs of simple Go code

Here are some proofs of Go code that operates on numbers, which demonstrate how to write specifications and all the basic automation tactics. The bodies of these functions use the heap for local variables, but notice how all the specifications can be written without points-to facts.

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
    wp_auto.
    wp_finish.
  Qed.

  (* The same proof, but carried out more manually. *)
  Lemma wp_Add_manual_proof (a b: w64) :
    {{{ is_pkg_init functional ∗ ⌜uint.Z a + uint.Z b < 2^64⌝ }}}
      @! functional.Add #a #b
    {{{ (c: w64), RET #c; ⌜uint.Z c = (uint.Z a + uint.Z b)%Z⌝  }}}.
  Proof.
    (* wp_start: *)
    iIntros (Φ) "[#? %Hoverflow] HΦ". (* wp_start introduces the [is_pkg_init for you] *)
    wp_func_call. wp_call.

    (* wp_auto: *)
    wp_alloc b_l as "b"; wp_pures.
    wp_alloc a_l as "a"; wp_pures.
    wp_load; wp_load; wp_pures.

    (* wp_finish: *)
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
    wp_finish.
  Qed.

  Lemma wp_Max (a b: w64) :
    {{{ is_pkg_init functional }}}
      @! functional.Max #a #b
    {{{ (c: w64), RET #c; ⌜uint.Z a ≤ uint.Z c ∧ uint.Z b ≤ uint.Z c⌝  }}}.
  Proof.
    wp_start.
    wp_auto.
    wp_if_destruct.
    - wp_finish.
    - wp_finish.
  Qed.

  Lemma wp_Midpoint (a b: w64) :
    {{{ is_pkg_init functional ∗ ⌜uint.Z a + uint.Z b < 2^64⌝ }}}
      @! functional.Midpoint #a #b
    {{{ (c: w64), RET #c; ⌜uint.Z c = (uint.Z a + uint.Z b) / 2⌝ }}}.
  Proof.
    wp_start as "%Hoverflow".
    wp_auto.
    wp_finish.
  Qed.

  Lemma wp_Midpoint2 (a b: w64) :
    {{{ is_pkg_init functional }}}
      @! functional.Midpoint2 #a #b
    {{{ (c: w64), RET #c; ⌜uint.Z c = (uint.Z a + uint.Z b) / 2⌝ }}}.
  Proof.
    wp_start.
    wp_auto.
    wp_if_destruct.
    - wp_finish.
    - wp_finish.
  Qed.

  Lemma wp_Arith (a b: w64) :
    {{{ is_pkg_init functional }}}
      @! functional.Arith #a #b
    {{{ (c: w64), RET #c; True }}}.
  Proof.
    wp_start.
    wp_auto.
    wp_if_destruct.
    - wp_finish.
    - wp_apply wp_Midpoint2.
      iIntros "%c %Heq".
      wp_auto.
      wp_finish.
  Qed.

  Lemma wp_SumN (n: w64) :
    {{{ is_pkg_init functional ∗ ⌜uint.Z n < 2^64-1⌝ }}}
      @! functional.SumN #n
    {{{ (m: w64), RET #m;
        ⌜uint.Z m = uint.Z n * (uint.Z n + 1) / 2⌝ }}}.
  Proof.
    wp_start as "%Hn_bound".
    wp_auto.

    iAssert (∃ (sum i: w64),
                "sum" :: sum_ptr ↦ sum ∗
                "i" :: i_ptr ↦ i ∗
                "%i_bound" :: ⌜uint.Z i ≤ uint.Z n + 1⌝ ∗
                "%Hsum_ok" :: ⌜uint.Z sum = (uint.Z i-1) * (uint.Z i) / 2⌝)%I
          with "[$sum $i]" as "HI".
    { iPureIntro. split; word. }
    wp_for "HI".
    wp_if_destruct.
    - wp_for_post.
      wp_finish.
      iPureIntro.
      assert (uint.Z i = (uint.Z n + 1)%Z) by word.
      word.
    - wp_apply wp_SumAssumeNoOverflow.
      iIntros (Hoverflow).
      wp_auto.
      wp_for_post.
      iFrame.
      iPureIntro.
      split_and!; try word.
      rewrite -> !word.unsigned_add_nowrap by word.
      word.
  Qed.

```

```rocq
End proof.
```
