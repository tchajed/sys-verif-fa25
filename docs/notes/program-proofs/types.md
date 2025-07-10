---
# Auto-generated from literate source. DO NOT EDIT.
tags:
  - literate
  - draft
---

::: warning Draft

This is still very much a work-in-progress.

:::

# Types in GooseLang

GooseLang pervasively uses types when interacting with memory (eg, loads, stores, pointers, slices). Here we explain how those types work.

```coq
(* enables defining structs with nice notation, something typically only done in
auto-generated code *)
Open Scope struct_scope.


```

Let's start with a classic Swap example, with pointers to integers:

```go
func Swap(x *uint64, y *uint64) {
  old_y := *y
  *y = *x
  *x = old_y
}
```

Here's what its goose translation looks like. Notice every load and store is annotated with its type, here `uint64T` for all four load/stores.

```coq
Definition Swap: val :=
    rec: <> "x" "y" :=
      let: "old_y" := ![#uint64T] "y" in
      "y" <-[#uint64T] ![#uint64T] "x";;
      "x" <-[#uint64T] "old_y";; #().

```

What is `uint64T`? It has type `go_type`, which is a Coq definition modeling a small subset of the Go type system:

```coq
Print go_type.
```

:::: note Output

```txt title="coq output"
Inductive go_type : Type :=
    boolT : go_type
  | uint8T : go_type
  | uint16T : go_type
  | uint32T : go_type
  | uint64T : go_type
  | stringT : go_type
  | arrayT : w64 → go_type → go_type
  | sliceT : go_type
  | interfaceT : go_type
  | structT : list (go_string * go_type) → go_type
  | ptrT : go_type
  | funcT : go_type.

Arguments arrayT n elem
Arguments structT decls%_list_scope%_struct_scope
```

::::

Types are being used in this translation as part of the _behavior_ or _semantics_ of this program. Typically types are part of what is formally called a _type system_: types as well as a way of checking that a program's type annotations are correct. The primary goal of a type system is to catch bugs before running your code (and beyond that, a sound type system can also give a _soundness guarantee_ about programs that type check, but that isn't covered in this class). There are some secondary benefits we won't talk about here, such as better performance from compiled code, and information hiding.

We do not have a type system that relates GooseLang expressions to these `ty`s. Instead, their main purpose is related to handling structs in memory, which we'll introduce next.

## Structs

The purpose of types in GooseLang is to model structs, and in particular references to structs. Let's walk through that.

As a running example, we'll use this Go struct:

```go
type Pair struct {
  x uint64
  y uint64
}
```

TODO: rewrite this to focus on what a user needs. In new goose this requires some explanation of how to use the generated outputs. The explanation below is not needed except for understanding the implementation of the Goose model in terms of GooseLang.

How is `Pair` represented as a value in GooseLang? To keep the language as simple as possible, it doesn't have a notion of a "struct value" or even fields. A `Pair` is actually represented as a tuple, with a `#()` tacked on at the end (don't worry about why - it just makes the recursive code that deals with struct fields easier). So what in Go would be `Pair { x: 2, y: 6 }` will be the value `(#2, (#6, #()))` in GooseLang.

When we have a `*Pair` - that is, a pointer to a Pair - things get more interesting. The problem we need to solve is that the code can take a `p *Pair` and use `&p.x` and `&p.y` as independent pointers; this is both safe and expected in concurrent code. Thus instead of having a single heap location with the whole Pair, the model splits it into two adjacent cells, one for `x` and one for `y` (the unit `#()` is not stored), and these cells can be independently written from different threads. The actual splitting is handled in the semantics of allocation, which "flattens" values.

However, if structs are flattened in memory, Goose has to emit non-trivial code for accessing fields individually, for example to model `*p.y` from the Pair pointer `p`. This is modeled by _implementing_ field access in GooseLang, using the field name "y" and the struct descriptor Pair, which together tell us that `y` will be one cell offset from the value of `p`. GooseLang has pointer arithmetic as a feature, even though it isn't a Go feature, so to read `y` we just dereference `p +ₗ 1` (the language uses the notation `+ₗ` for pointer arithmetic to distinguish it from regular addition).

The actual implementation doesn't emit `p +ₗ 1`, because that would result in very hard to read GooseLang code. Instead, it emits a Gallina function `struct.loadField Pair "y" #p`, where `Pair` is exactly the descriptor above, "x" is a string that is used to find the right offset within `Pair`, and `#p` is the pointer to be loaded from.

TODO:

- explain how a struct is loaded
- explain how points-to fact for a struct needs to account for different fields
- explain how struct points-to is implemented in terms of a primitive single-cell points-to (which we never need as users)
- explain how store needs to maintain the type invariant in the struct points-to and thus requires a type proof
