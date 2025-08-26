---
# Auto-generated from literate source. DO NOT EDIT.
tags: literate
shortTitle: Integers
---

# Integers in GooseLang

```rocq
From sys_verif.program_proof Require Import prelude empty_ffi.
From New.generatedproof.sys_verif_code Require Import functional.
Section goose.
Context `{hG: !heapGS Σ}.

```

You'll be pervasively working with integers in GooseLang. A few hints will help make sense of all the types and functions for reasoning about them in program proofs, in Coq.

First, Goose primarily supports the Go type `uint64`, unsigned 64-bit integers. There is also support for `uint32` and preliminary support for signed integers `int64`, but it's easiest if you stick to `uint64`. Note that most Go code would use `int` as the basic integer type, which is a signed integer whose size matches the architecture.

Next, the type `w64` represents a 64-bit integer value. This is used both in GooseLang and in proofs.

In GooseLang, to use a w64 we have to turn it into a value. This is almost always written `#x`. Technically, this produces the term `LitV (LitInt x)`, but `LitInt` is inserted implicitly (this is the Coq's coercions feature) and `#` is notation for `LitV`.

```rocq
Set Printing Coercions. Unset Printing Notations.
Eval simpl in (fun (x: w64) => #x).
```

:::: note Output

```txt
     = fun x : w64 => to_val x
     : forall _ : w64, val
```

::::

```rocq
Unset Printing Coercions. Set Printing Notations.


```

## w64 to Z and back

Reasoning about integers is always done via their mathematical representation as a `Z`, a signed integer.

- `uint.Z : w64 → Z` gives the abstract value of a concrete integer.
- `W64 : Z → w64` converts an abstract value to a concrete integer. This ends up taking the value mod $2^{64}$ since w64 is bounded.
- `uint.nat : w64 → nat` is a shorthand for `fun x => Z.of_nat (uint.Z x)`, for cases where you need to use a `nat`. This happens often because the list functions all require `nat` and not `Z`. (I hope to eventually fix this in a future version of GooseLang.)

## word tactic

The `word` tactic is an extension of `lia` that will help you prove goals involving words and `uint.Z`, including handling overflow reasoning.

The word tactic, among other things, uses lemmas like `word.unsigned_add` and `word.unsigned_mul` to reason about the value of `uint.Z (word.add x y)` and `uint.Z (word.mul x y)`. In some cases you may want to `rewrite` with those lemmas directly, especially if you want to do something unusual with overflow, or if `word` isn't able to prove that overflow doesn't occur.

## An example specification

You can see all of this integer reasoning in action in this proof of `Add`, a function which takes two `uint64`s and just returns their sum.

We need `%Z` in the postcondition to force parsing using the Z notations (`+` is overloaded and is otherwise interpreted as something for types).

This style of postcondition is common with integers: we say there exists a `z: w64` that is returned, and then describe `uint.Z z`. This avoids having to specifically write down how the word itself is constructed, and we can just use operations on Z.

```rocq
Lemma wp_Add_bounded (x y: w64) :
  {{{ ⌜uint.Z x + uint.Z y < 2^64⌝ }}}
    functional.Addⁱᵐᵖˡ #x #y
  {{{ (z: w64), RET #z; ⌜uint.Z z = (uint.Z x + uint.Z y)%Z⌝ }}}.
Proof.
  wp_start as "%Hbound". wp_call.
  wp_alloc b_l as "b". wp_pures.
  wp_alloc a_l as "a". wp_pures.
  wp_load. wp_load. wp_pures.
```

:::: info Goal

```txt
  Σ : gFunctors
  hG : heapGS Σ
  x, y : w64
  Φ : val → iPropI Σ
  Hbound : uint.Z x + uint.Z y < 2 ^ 64
  b_l, a_l : loc
  ============================
  "HΦ" : ∀ z : w64, ⌜uint.Z z = (uint.Z x + uint.Z y)%Z⌝ -∗ Φ (# z)
  "b" : b_l ↦ y
  "a" : a_l ↦ x
  --------------------------------------∗
  Φ (# (word.add x y))
```

::::

You can see in this goal that the specific word being returned is `word.add x y`.

```rocq
  iApply "HΦ".
  iPureIntro.
```

:::: info Goal

```txt
  Σ : gFunctors
  hG : heapGS Σ
  x, y : w64
  Φ : val → iPropI Σ
  Hbound : uint.Z x + uint.Z y < 2 ^ 64
  b_l, a_l : loc
  ============================
  uint.Z (word.add x y) = uint.Z x + uint.Z y
```

::::

This goal is only true because the sum doesn't overflow - in general `uint.Z (word.add x y) = (uint.Z x + uint.Z y) % 2^64`.

```rocq
  word.
Qed.

```

If for whatever reason you want to just specify the exact word being returned, you can use `word.add` directly, but it's not common to want this.

```rocq
Lemma wp_Add_general (x y: w64) :
  {{{ True }}}
    functional.Addⁱᵐᵖˡ #x #y
  {{{ RET #(word.add x y); True }}}.
Proof.
  wp_start as "_". wp_call.
  wp_alloc b_l as "b". wp_pures.
  wp_alloc a_l as "a". wp_pures.
  wp_load. wp_load. wp_pures.
  iApply "HΦ". done.
Qed.

End goose.
```
