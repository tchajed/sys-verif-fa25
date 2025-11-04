---
# Auto-generated from literate source. DO NOT EDIT.
tags:
  - literate
---

```rocq
From sys_verif.program_proof Require Import prelude empty_ffi.

```

# Named propositions

We used _named propositions_ in Iris, which have the syntax `"H" :: P` where `P: iProp Σ`. The name in a named proposition has no effect on its meaning; it's only a convenience for using the proposition.

The basic idea is that a proposition `"HP" :: P ∗ "HQ" :: Q` is like `P ∗ Q`, except that if you used the `iNamed` to destruct it, it "knows" to name the conjuncts `"HP"` and `"HQ"`. Putting the names in the definitions has three advantages:

- The names are often easier to come up with right next to the statements in the definition rather than when you're destructing something.
- If you destruct the same definition several times in different proofs, it's convenient to right the names once and nice to have consistency across proofs.
- If a definition changes its easier to add some new names for the new conjuncts and update the proofs compared to changing all the `iDestruct` calls.

Named propositions are typically used in three places:

- In definitions (especially representation predicates), to name each conjunct.
- In loop invariants, again to name the conjuncts.
- After `iApply struct_fields_split`, the resulting hypothesis internally uses named propositions to automatically name the conjuncts according to the field names.

The names are actually Iris intro patterns. We tend to use this power in only two ways: plain old `"HP"` is an intro pattern that just names the conjunct, and `"%H"` is an intro pattern that produces the Rocq hypothesis `H` rather than a separation logic hypothesis.

See the documentation in the source code at [named_props.v](https://github.com/tchajed/iris-named-props/blob/main/src/named_props.v) for more details on the API.

You may see a use of `iNamed 1`, which is just `iIntros "Hfresh"; iNamed "Hfresh"`; if the goal is `foo -∗ ...` it applied the named struct to `foo` after introducing it. (This syntax may seem mysterious but it mirrors a Rocq feature where `destruct 1` will destruct the first premise if the goal is `P → ...`.)

```rocq
Section goose.
Context `{!heapGS Σ}.

Lemma simple_inamed (P Q: iProp Σ) :
  ("HP" ∷ P ∗ "HQ" ∷ Q) -∗ P.
Proof.
  iIntros "H". iNamed "H".
```

:::: info Goal diff

```txt
  P, Q : iProp Σ
  ============================
  "H" : "HP" ∷ P ∗ "HQ" ∷ Q // [!code --]
  "HP" : P // [!code ++]
  "HQ" : Q // [!code ++]
  --------------------------------------∗
  P
```

::::

```rocq
  iExact "HP".
Qed.

Definition own_foo l: iProp Σ :=
  ∃ (p r: w64),
  "HP" :: l ↦ p ∗
  "HR" :: (l +ₗ 2) ↦ r ∗
  "%Hbound" :: ⌜uint.Z p < uint.Z r⌝.

Lemma own_foo_read_P l :
  own_foo l -∗ ∃ (p: w64), l ↦ p.
Proof.
  iIntros "H".
  iNamed "H".
```

:::: info Goal diff

```txt
  l : loc
  p, r : w64 // [!code ++]
  Hbound : uint.Z p < uint.Z r // [!code ++]
  ============================
  "H" : own_foo l // [!code --]
  "HP" : l ↦ p // [!code ++]
  "HR" : (l +ₗ 2) ↦ r // [!code ++]
  --------------------------------------∗
  ∃ p : w64, l ↦ p // [!code --]
  ∃ p0 : w64, l ↦ p0 // [!code ++]
```

::::

```rocq
  iFrame.
Qed.

End goose.
```
