---
# Auto-generated from literate source. DO NOT EDIT.
category: demo
tags: literate
order: 4
pageInfo: ["Date", "Category", "Tag"]
shortTitle: "Demo: FastExp"
---

# Demo: FastExp loop invariant

We verify an efficient implementation of exponentiation, which requires a clever loop invariant.

The code being verified is the following:

```go
// FastExp returns b to the power of n0
func FastExp(b uint64, n0 uint64) uint64 {
	var a uint64 = 1
	var c = b
	var n = n0
	for n > 0 {
		if n%2 == 1 {
			a = a * c
			n = n / 2
		} else {
			n = n / 2
		}
		c = c * c
	}
	return a
}
```

---

```rocq
From sys_verif.program_proof Require Import prelude.

From sys_verif.program_proof Require Import functional_init.
From New.proof Require Import std.

#[local] Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Add Printing Coercion Z.of_nat.

(* some helper lemmas about arithmetic *)

(* b^n is defined by the Coq standard library. Let's show that it has the same
recursive definition we expect. *)
Lemma Z_pow_recursion (n: Z) :
  0 ≤ n →
  2^n = if decide (n = 0) then 1 else 2*2^(n-1).
Proof.
  intros Hle.
  destruct (decide _).
  - subst. reflexivity.
  - (* this proof strategy requires some cleverness: we basically just need to
    enable Z.pow_add_r to do the main work *)
    replace n with (1 + (n-1)) at 1 by lia.
    rewrite -> Z.pow_add_r by lia.
    reflexivity.
Qed.

(* For some reason Z.mod_mul_r is actually about `rem` and `quot`, which are
like div and mod but have different behavior on negative numbers. This is
probably an upstream bug in Coq (at the very least the proper lemma should be
provided, if not with the right name) *)
Lemma Zmod_mul_r a b c :
  0 ≤ a →
  0 ≤ b →
  0 ≤ c →
  a `mod` (b * c) = a `mod` b + b * (a `div` b) `mod` c.
Proof.
  intros.
  (* these special cases do go through, but the general lemmas we use below
  don't work in them *)
  destruct (decide (b = 0)); subst.
  { lia. }
  destruct (decide (c = 0)); subst.
  { lia. }
  (* we're using [nia] rather than [lia] here since it's a non-linear arithmetic
  solver; it can handle some uses of multiplication and division  *)
  rewrite <- !Z.rem_mod_nonneg by nia.
  rewrite <- !Z.quot_div_nonneg by nia.
  rewrite -> Z.mod_mul_r by nia.
  nia.
Qed.

(* similar to Z.div_div but remove some unneeded side conditions *)
Lemma Zdiv_mul_r a b c :
  0 ≤ c →
  a `div` (b * c) = (a `div` b) `div` c.
Proof.
  intros.
  destruct (decide (c = 0)); subst.
  { lia. }
  destruct (decide (b = 0)).
  { subst.
    nia. }
  rewrite Z.div_div //.
  lia.
Qed.

(* It's helpful to prove this fairly specialized lemma to show that an exponent
doesn't overflow by transitivity. This proof has to work around the edge case of
b being 0. *)
Lemma no_overflow_mono b n1 n2 :
  b^n1 < 2^64 →
  0 ≤ b →
  0 ≤ n1 →
  0 < n2 →
  n2 ≤ n1 →
  b^n2 < 2^64.
Proof.
  intros.
  destruct (decide (b = 0)); subst.
  { rewrite -> Z.pow_0_l by lia.
    lia. }
  eapply Z.le_lt_trans; [ | by eauto ].
  apply Z.pow_le_mono_r; lia.
Qed.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx: GoContext}.

```

This is the invariant that makes the proof work. The inputs all directly correspond to the code's variables. Remember that [n0] is the initial value and we're computing [b^n0] while [n] is a mutable variable.

```rocq
Definition fast_exp_inv (b n0 a c n: w64) :=
  (* [i] is the iteration count, which isn't tracked in the code *)
  ∃ (i: Z),
  let b := uint.Z b in
  let n0 := uint.Z n0 in
  let a := uint.Z a in
  let c := uint.Z c in
  let n := uint.Z n in
  0 ≤ i ∧

  (* The code works by processing [n0] one bit at a time, accumulating the
  result in [a]. [n] starts out at [n0], then on each iteration its divided by
  two to process the remaining bits.

  It turns out to be easy to express the accumulator with the iteration count:
  it's [b^(n0 % (2^i))] - the exponent is the i low-order bits of [n0]. [n] is
  always [n0 / (2^i)], the high-order bits of [n0]. Finally, when [n%2 = 1], the
  code needs to incorporate one more bit of [n0], which it does by multiplying
  by [c], which has the value [b^(2^i)] (this last part is easy to see in
  isolation - every loop iteration does [c := c * c]).
   *)

  (* One subtlety about [c]: it actually might overflow on the last iteration,
  but the overflowed result isn't used, so we only state this when [0 < n] and
  the loop is still ongoing. Luckily we don't need [c] when the loop exits, only
  [a]. *)
  (0 < n → c = b^(2^i)) ∧
  n = n0 `div` (2^i) ∧
  a = b^(n0 `mod` (2^i)).

```

The main difficult reasoning about this code is to show that the above loop invariant is (1) `fast_exp_inv_init`, the invariant holds with the code's initial values, (2) `fast_exp_inv_done`, when the loop exits, `a` has the final result we want, (3) `fast_exp_inv_odd` and `fast_exp_inv_even`, which show the invariant is preserved by the body (with the proof divided into two cases, one for each branch).

All of these proofs don't have any program reasoning, it's all just mathematical proofs about arithmetic (albeit including the complications of finite-precision machine arithmetic).

```rocq
Lemma fast_exp_inv_init b n0 :
  fast_exp_inv b n0 (W64 1) b n0.
Proof.
  exists 0; simpl.
  split_and!; try nia.
  rewrite Z.pow_0_r Z.mod_1_r.
  rewrite Z.pow_0_r.
  word.
Qed.

Lemma fast_exp_inv_done b n0 a c n :
  uint.Z n = 0 →
  fast_exp_inv b n0 a c n →
  uint.Z a = (uint.Z b)^(uint.Z n0).
Proof.
  intros Hn Hinv.
  destruct Hinv as [i (H1 & H2 & H3 & H4)].
  rewrite Hn in H2 H3.
  rewrite H4.
  f_equal.
  (* this is the reason the proof goes through (though the assertion is not needed) *)
  assert (uint.Z n0 =
            (2^i) * uint.Z n0 `div` (2^i) + uint.Z n0 `mod` (2^i)) by lia.
  lia.
Qed.

```

This proofs takes into account integer overflow, starting only with the assumption that the final exponentiation doesn't overflow a Go `uint64` (an unsigned 64-bit integer), and we need that non-overflow for this theorem to be true.

```rocq
Lemma fast_exp_inv_odd b n0 a c n :
  (uint.Z b)^(uint.Z n0) < 2^64 →
  uint.Z n `mod` 2 = 1 →
  0 < uint.Z n →
  fast_exp_inv b n0 a c n →
  fast_exp_inv b n0 (word.mul a c) (word.mul c c) (word.divu n (W64 2)).
Proof.
  intros Hoverflow Hnmod2 Hcontinue Hinv.
  destruct Hinv as [i Hinv].
  exists (1 + i).
  simpl.

  destruct Hinv as (H1 & H2 & H3 & H4).
  rewrite -> word.unsigned_divu_nowrap by word.
  change (uint.Z (W64 2)) with 2.

  assert (uint.Z c * uint.Z c = uint.Z b ^ (2^(1+i))) as Hcc.
  { rewrite -> H2 by auto.
    rewrite <- Z.pow_add_r by lia.
    f_equal.
    rewrite -> Z.pow_add_r; lia.
  }

  split_and!.
  - lia.
  - intros ?.
    rewrite word.unsigned_mul_nowrap.
    { (* [c*c] overflow *)
      rewrite Hcc.
      eapply no_overflow_mono; [ eassumption | word | word | word | ].
      replace (2^(1+i)) with (2^i + 2^i) by (rewrite Z.pow_add_r; lia).
      nia. }
    done. (* proven above *)
  - rewrite H3.
    rewrite -> Z.div_div by lia.
    f_equal.
    rewrite Z.pow_add_r; lia.
  - rewrite word.unsigned_mul_nowrap.
    { (* need to show [a*c] doesn't overflow *)
      rewrite H4.
      rewrite -> H2 by lia.
      rewrite <- Z.pow_add_r by lia.
      eapply no_overflow_mono; [ eassumption | word | word | word | ].
      nia.
    }
    rewrite H4 H2; auto.
    rewrite <- Z.pow_add_r by lia.
    f_equal.

    (* we need Zmod_mul_r with 2^i on the inside and 2 on the outside, so
      reverse these *)
    replace (1 + i) with (i + 1) by lia.
    rewrite -> Z.pow_add_r by lia.
    change (2^1) with 2.
    rewrite -> Zmod_mul_r by word.
    rewrite -H3 Hnmod2.
    lia.
Qed.

Lemma fast_exp_inv_even (b n0 a c n: w64) :
  (uint.Z b)^(uint.Z n0) < 2^64 →
  uint.Z n `mod` 2 = 0 →
  0 < uint.Z n →
  fast_exp_inv b n0 a c n →
  fast_exp_inv b n0 a (word.mul c c) (word.divu n (W64 2)).
Proof.
  intros Hoverflow Hnmod2 Hcontinue Hinv.
  destruct Hinv as [i Hinv].
  exists (1 + i).
  simpl.

  destruct Hinv as (H1 & H2 & H3 & H4).
  rewrite -> word.unsigned_divu_nowrap by word.
  change (uint.Z (W64 2)) with 2.
  assert (uint.Z c * uint.Z c = uint.Z b ^ (2^(1+i))) as Hcc.
  { rewrite -> H2 by auto.
    rewrite <- Z.pow_add_r by lia.
    f_equal.
    rewrite -> Z.pow_add_r; lia.
  }

  split_and!.

  - lia.
  - intros ?.
    rewrite word.unsigned_mul_nowrap.
    { rewrite Hcc.
      eapply no_overflow_mono; [ eassumption | word | word | word | ].
      replace (2^(1+i)) with (2^i + 2^i) by (rewrite Z.pow_add_r; lia).
      nia. }
    done. (* proven above *)
  - rewrite H3.
    rewrite -> Z.div_div by lia.
    f_equal.
    rewrite Z.pow_add_r; lia.
  - rewrite H4.
    f_equal.

    (* we need Zmod_mul_r with 2^i on the inside and 2 on the outside, so
    reverse these *)
    replace (1 + i) with (i + 1) by lia.
    rewrite -> Z.pow_add_r by lia.
    change (2^1) with 2.
    rewrite -> Zmod_mul_r by word.
    rewrite -H3 Hnmod2.
    lia.
Qed.

```

`wp_FastExp` is the specification we prove for `FastExp`. Since this function takes plain integers as inputs and returns an integer, the specification doesn't involve anything in separation logic; its allocations are all hidden from the caller. All we need is a precondition asserting the final result will not overflow and a postcondition that the return value is indeed a 64-bit number with the right value.

```rocq
Lemma wp_FastExp (b n0: w64) :
  {{{ is_pkg_init functional ∗ ⌜(uint.Z b)^(uint.Z n0) < 2^64⌝  }}}
    @! functional.FastExp #b #n0
  {{{ (e: w64), RET #e; ⌜uint.Z e = (uint.Z b)^(uint.Z n0)⌝ }}}.
Proof.
  wp_start as "%Hoverflow".
  wp_auto.
  iAssert (∃ (a c n: w64),
             "a" ∷ a_ptr ↦ a ∗
             "c" ∷ c_ptr ↦ c ∗
             "n" ∷ n_ptr ↦ n ∗
             "%Hinv" ∷ ⌜fast_exp_inv b n0 a c n⌝
          )%I with "[$a $c $n]" as "inv".
  {
    iPureIntro.
    apply fast_exp_inv_init.
  }
  wp_for.
  iNamed "inv".
  wp_auto.
  wp_if_destruct.
  - wp_if_destruct.
    + wp_for_post.
      iFrame.
      iPureIntro.
      apply fast_exp_inv_odd; auto.
      apply (f_equal uint.Z) in e.
      word.
    + wp_for_post.
      iFrame.
      iPureIntro.
      apply fast_exp_inv_even; auto.
      assert (uint.Z n `mod` 2 ≠ 1); [ | lia ].
      intros H.
      contradiction n1.
      word.
  - wp_finish.
    iPureIntro.
    eapply fast_exp_inv_done; [ | eauto ].
    word.
Qed.

End proof.
```
