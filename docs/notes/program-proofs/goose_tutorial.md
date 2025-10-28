<!-- Auto-generated from literate source. DO NOT EDIT. -->

# Goose tutorial

Start here to learn how Goose works. Use this as a reference.

NOTE: this is mostly notes on what needs to be written, not the actual guide yet.

```rocq
From sys_verif.program_proof Require Import prelude empty_ffi.

```

## new goose

`IntoVal V` describes how a Gallina term represents a GooseLang value. First, some "base instances" are available: `IntoVal w64`, `IntoVal bool`. Second, each GooseLang struct is given a Gallina struct for its raw data.

`↦` is `typed_pointsto`. Signature is `l ↦ v` where `IntoVal V`, `l: loc` and `v: V`. Important that the type of `v` be constrained for type inference. Also have `l ↦{dq} v` for fractional permissions.

Reading Rocq goals: need to understand somewhat the meaning of `exception_do` and the monadic notations, but it's not actually super important.

Use `rewrite -!default_val_eq_zero_val` to process `zero_val` (although this should not be needed if you're using `wp_start`)
