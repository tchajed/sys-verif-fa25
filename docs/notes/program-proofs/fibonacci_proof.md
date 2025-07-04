---
# Auto-generated from literate source. DO NOT EDIT.
category: demo
tags: literate
order: -1
pageInfo: ["Date", "Category", "Tag"]
shortTitle: "Demo: fibonacci"
---

# Demo: verifying fibonacci function

> The Coq code for this file is at [src/sys_verif/program_proof/demos/fibonacci_proof.v](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/src/sys_verif/program_proof/demos/fibonacci_proof.v).

The code in [go/functional/functional.go](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/go/functional/functional.go) implements `func Fibonacci(n uint6) uint64`, computing the nth Fibonacci number.

We prove this function correct, proving that the imperative, loop-based implementation Go is equivalent to a recursive, functional implementation in Gallina.

```coq
From sys_verif.program_proof Require Import prelude empty_ffi.
From Goose.sys_verif_code Require Import functional.

Section proof.
Context `{hG: !heapGS Σ}.

Fixpoint fibonacci (n: nat): nat :=
  match n with
  | 0 => 0
  | 1 => 1
  (* a little care is needed for Coq to accept that this function terminates *)
  | S (S n_minus_2 as n_minus_1) => fibonacci n_minus_2 + fibonacci n_minus_1
  end%nat.

```

We will need some helper lemmas. These are only required because the specification will assume that the final result doesn't overflow, and we will use that to show that the intermediate results also don't overflow.

```coq
Lemma fibonacci_S i :
  (1 ≤ i)%nat →
  fibonacci (S i) = (fibonacci i + fibonacci (i-1))%nat.
Proof.
  intros Hle.
  destruct i; simpl.
  { lia. (* contradicts assumption *) }
  replace (i - 0)%nat with i by lia.
  lia.
Qed.

Lemma fibonacci_monotonic i1 i2 :
  (i1 ≤ i2)%nat →
  fibonacci i1 ≤ fibonacci i2.
Proof.
  intros Hle.
  destruct (decide (i1 = i2)).
  { subst; lia. }

  assert (∃ d, i2 = S (d + i1)) as H.
  { exists (i2 - i1 - 1)%nat. lia. }
  destruct H as [d ?]; subst.

  move: Hle.
  clear.
  induction d.
  - destruct i1; simpl; lia.
  - simpl in *; lia.
Qed.

```

Here is the statement of what it means for `Fibonacci` (the Go function) to be correct.

```coq
Lemma wp_Fibonacci (n: w64) :
  {{{ ⌜Z.of_nat (fibonacci (uint.nat n)) < 2^64⌝ }}}
    Fibonacci #n
  {{{ (c: w64), RET #c; ⌜uint.nat c = fibonacci (uint.nat n)⌝ }}}.
Proof.
  wp_start as "%Hoverflow".
  wp_pures.
  wp_if_destruct.
  { iModIntro.
    iApply "HΦ".
    iPureIntro.
    reflexivity.
  }
  wp_alloc fib_prev as "fib_prev".
  wp_alloc fib_cur as "fib_cur".
  wp_alloc i_l as "i".
  wp_pures.

```

The core of the proof's argument is this loop invariant about the `prev` and `cur` variables.

```coq
  wp_apply (wp_forUpto'
            (λ i, ∃ (prev cur: w64),
              "fib_prev" ∷ fib_prev ↦[uint64T] #prev ∗
              "fib_cur" ∷ fib_cur ↦[uint64T] #cur ∗
              "%Hi_ge" ∷ ⌜1 ≤ uint.Z i⌝ ∗
              "%Hprev" ∷ ⌜uint.nat prev = fibonacci (uint.nat i - 1)⌝ ∗
              "%Hcur" ∷ ⌜uint.nat cur = fibonacci (uint.nat i)⌝
            )%I
            with "[$i $fib_prev $fib_cur]").
  - iPureIntro.
    split.
    { word. }
    split.
    { word. }
    split.
    { reflexivity. }
    reflexivity.
  - clear Φ.
    iIntros "!>" (i Φ) "[IH (i & %Hle)] HΦ".
    iNamed "IH".
    wp_pures.
    repeat (wp_load || wp_store || wp_pures).
    iModIntro.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    split.
    + word.
    + split.
      { rewrite Hcur. f_equal; word. }
      replace (uint.nat (word.add i (W64 1))) with
        (S (uint.nat i)) by word.
      rewrite fibonacci_S; [ | word ].
      (* we need to show the [word.add] doesn't overflow to finish the proof *)
      assert (uint.Z cur + uint.Z prev < 2^64) as Hsum.
      {
        (* to prove this, we'll use the fact that [uint.nat cur + uint.nat
      prev = fibonacci (S i)], and that [fibonacci] is monotonic. We know that
      [i < n] as part of the loop invariant. *)
        pose proof (fibonacci_monotonic (S (uint.nat i)) (uint.nat n)) as Hi_n.
        rewrite -> fibonacci_S in Hi_n by word.
        word. }
      word.
  - iIntros "[IH i]". iNamed "IH".
    wp_load.
    iModIntro.
    iApply "HΦ".
    auto.
Qed.

End proof.
```
