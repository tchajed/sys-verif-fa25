---
# Auto-generated from literate source. DO NOT EDIT.
tags:
- literate
- draft
---

::: warning Draft under construction
This is still very much a work-in-progress.
:::


```coq
(* enables defining structs with nice notation, something typically only done in
auto-generated code *)
Open Scope struct_scope.

```

# Types in GooseLang

GooseLang pervasively uses types when interacting with memory (eg, loads,
stores, pointers, slices). Here we explain how those types work.


Let's start with a classic Swap example, with pointers to integers:

```go
func Swap(x *uint64, y *uint64) {
  old_y := *y
  *y = *x
  *x = old_y
}
```

Here's what its goose translation looks like. Notice every load and store is
annotated with its type, here `uint64T` for all four load/stores.

```coq
Definition Swap: val :=
    rec: <> "x" "y" :=
      let: "old_y" := ![uint64T] "y" in
      "y" <-[uint64T] ![uint64T] "x";;
      "x" <-[uint64T] "old_y";; #().

```

What is `uint64T`? It has type `ty`, which is a Coq definition modeling a
small subset of the Go type system:

```coq
Print ty.
```


:::: note Output
```txt title="coq output"
Inductive ty (val_tys : val_types) : Type :=
    baseT : typing.base_ty → ty
  | prodT : ty → ty → ty
  | listT : ty → ty
  | sumT : ty → ty → ty
  | arrowT : ty → ty → ty
  | arrayT : ty → ty
  | ptrT : ty
  | structRefT : list ty → ty
  | mapValT : ty → ty → ty
  | chanValT : ty → ty
  | extT : ext_tys → ty
  | prophT : ty.

Arguments ty {val_tys}
Arguments baseT {val_tys} t
Arguments prodT {val_tys} (t1 t2)%heap_type
Arguments listT {val_tys} t1%heap_type
Arguments sumT {val_tys} (t1 t2)%heap_type
Arguments arrowT {val_tys} (t1 t2)%heap_type
Arguments arrayT {val_tys} t%heap_type
Arguments ptrT {val_tys}
Arguments structRefT {val_tys} ts%list_scope
Arguments mapValT {val_tys} (kt vt)%heap_type
Arguments chanValT {val_tys} vt%heap_type
Arguments extT {val_tys} x
Arguments prophT {val_tys}
```
::::
`uint64T` itself is an example of a `baseT`.
Types are being used in this translation as part of the _behavior_ or
_semantics_ of this program. Typically types are part of what is formally called
a _type system_: types as well as a way of checking that a program's type
annotations are correct. The primary goal of a type system is to catch bugs
before running your code (and beyond that, a sound type system can also give a
_soundness guarantee_ about programs that type check, but that isn't covered in
this class). There are some secondary benefits we won't talk about here, such as
better performance from compiled code, and information hiding.

We do not have a type system that relates GooseLang expressions to these `ty`s.
Instead, their main purpose is related to handling structs in memory, which
we'll introduce next.

## Structs

The purpose of types in GooseLang is to model structs, and in particular
references to structs. Let's walk through that.

As a running example, we'll use this Go struct:

```go
type Pair struct {
  x uint64
  y uint64
}
```

What goose translates this struct to is a struct _descriptor_, which is a
list of fields and types for the struct.

```coq
Definition Pair := struct.decl [
  "x" :: uint64T;
  "y" :: uint64T
].

```

TODO: oops, this is getting too much into the motivation. Explain axiomatically
starting from what a struct points-to is.

How is `Pair` represented as a value in GooseLang? To keep the language as
simple as possible, it doesn't have a notion of a "struct value" or even fields.
A `Pair` is actually represented as a tuple, with a `#()` tacked on at the end
(don't worry about why - it just makes the recursive code that deals with struct
fields easier). So what in Go would be `Pair { x: 2, y: 6 }` will be the value
`(#2, (#6, #()))` in GooseLang.

When we have a `*Pair` - that is, a pointer to a Pair - things get more
interesting. The problem we need to solve is that the code can take a `p *Pair`
and use `&p.x` and `&p.y` as independent pointers; this is both safe and
expected in concurrent code. Thus instead of having a single heap location with
the whole Pair, the model splits it into two adjacent cells, one for `x` and one
for `y` (the unit `#()` is not stored), and these cells can be independently
written from different threads. The actual splitting is handled in the semantics
of allocation, which "flattens" values.


However, if structs are flattened in memory, Goose has to emit non-trivial code
for accessing fields individually, for example to model `*p.y` from the Pair
pointer `p`. This is modeled by _implementing_ field access in GooseLang, using
the field name "y" and the struct descriptor Pair, which together tell us that
`y` will be one cell offset from the value of `p`. GooseLang has pointer
arithmetic as a feature, even though it isn't a Go feature, so to read `y` we
just dereference `p +ₗ 1` (the language uses the notation `+ₗ` for pointer
arithmetic to distinguish it from regular addition).

The actual implementation doesn't emit `p +ₗ 1`, because that would result in
very hard to read GooseLang code. Instead, it emits a Gallina function
`struct.loadField Pair "y" #p`, where `Pair` is exactly the descriptor above,
"x" is a string that is used to find the right offset within `Pair`, and `#p` is
the pointer to be loaded from.

TODO:
- explain how a struct is loaded
- explain how points-to fact for a struct needs to account for different fields
- explain how struct points-to is implemented in terms of a primitive
  single-cell points-to (which we never need as users)
- explain how store needs to maintain the type invariant in the struct points-to
  and thus requires a type proof


