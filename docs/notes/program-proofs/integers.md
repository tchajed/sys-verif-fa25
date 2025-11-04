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

You'll be pervasively working with integers in GooseLang. A few hints will help make sense of all the types and functions for reasoning about them in program proofs, in Rocq.

On the Go side, Goose supports the various integer types: the most commonly used are `int`, which is a signed 64-bit integer (we assume a 64-bit architecture), `uint64` is an unsigned 64-bit integer, and `uint32` is an unsigned 32-bit integer.

In Rocq, both signed and unsigned integers are represented using the `w64` type from a library for finite precision integers. The difference between signed and unsigned is reflected in how we use that type: if `x: w64` in Rocq, then `uint.Z x : Z` converts it to an integer treating it as _unsigned_, while `sint.Z x : Z` converts it as a _signed_ integer (note that **u**int stands for unsigned int and **s**int stands for signed int).

In GooseLang, to use a w64 or w32 we have to turn it into a value. This is done using `#x`, the way we convert any Gallina value into GooseLang.

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

- `uint.Z : w64 → Z` gives the abstract value of a concrete integer as an unsigned integer.
- `sint.Z : w64 → Z` gives the abstract value of a concrete integer as an signed integer.
- `W64 : Z → w64` converts an abstract value to a concrete integer. This ends up taking the value mod $2^{64}$ since w64 is bounded. Signed integers are represented using two's complement.
- `uint.nat : w64 → nat` is a shorthand for `fun x => Z.of_nat (uint.Z x)`, for cases where you need to use a `nat`. This happens often because the list functions all require `nat` and not `Z`. (I hope to eventually fix this in a future version of GooseLang.)
- `sint.nat : w64 → nat` is similarly `fun x => Z.of_nat (sint.Z x)` (but note this somewhat unintuitively takes the absolute value for negative numbers).

## word tactic

The `word` tactic will help you prove goals involving words, `uint.Z`, and `sint.Z`, including handling overflow reasoning. It is a wrapper around Rocq's `lia` tactic, a powerful automation engine for integer arithmetic.

The word tactic, among other things, uses lemmas like `word.unsigned_add` and `word.unsigned_mul` to reason about the value of `uint.Z (word.add x y)` and `uint.Z (word.mul x y)`. In some cases you will need to `rewrite` with those lemmas directly, especially if you want to do something unusual with overflow, or if `word` isn't able to prove that overflow doesn't occur.

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
