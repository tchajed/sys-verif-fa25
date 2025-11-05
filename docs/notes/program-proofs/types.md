---
# Auto-generated from literate source. DO NOT EDIT.
tags: literate
date: 2025-11-03 8:00:00 -5
---

# Types in Perennial and Goose

We use various types in Perennial to represent Go data. Working with Goose, you immediately encounter some correspondences: for example, a Go integer of type `int` is represented as a `w64`, and a Go boolean `bool` is represented as a Rocq `bool`. This correspondence becomes especially interesting with structs.

You also encounter _type identifiers_ when setting up proofs for methods, where the Hoare triples need to supply which type the method is on, and whether it is for the type or a pointer to the type.

This reference explains how the type setup works.

It will help a good deal in following the details here to understand typeclasses in Rocq. Practically to do proofs you might not interact with them much, but some understanding will help you understand error messages when things go wrong. A good but long tutorial is included in [Software Foundations](https://softwarefoundations.cis.upenn.edu/qc-current/Typeclasses.html).

The most important typeclass for Goose is `IntoVal V`. Its definition is the following:

```rocq
Class IntoVal (V: Type) :=
  { to_val : V → val }.
```

One way to think about this typeclass is as "classifying" types `V` that can be converted to values: those will be the types that implement this class. For this particular class, implementing it means that values of type `V` can be represented in GooseLang, either using the supported literals (locations, integers, booleans, etc.) or as a composite value using a tuple.

We can talk about whether `IntoVal Foo` is implemented for some specific type `Foo`. These implementations are called _instances_ and are provided with `Instance`. If there's an instance, then `to_val v` will work and give the GooseLang representation of `v`. The `IntoVal` typeclass is implemented (read: has instances) for various types. `IntoVal w64`, `IntoVal bool`, `IntoVal loc` all exist. We will see later how IntoVal supports Go structs.

Since this typeclass is used so pervasively, Perennial has a notation `#v` for `to_val v`. A key principle in Goose is that _all GooseLang values_ are always of the form `#v` or otherwise internally use `to_val` (including the ones you write in specifications), so we never have Rocq variables of type `val` directly.

Here's a table of the basic `IntoVal` instances in Perennial:

| Go type          | Rocq type     |
| :--------------- | :------------ |
| `int`            | `w64`         |
| `uint64`         | `w64`         |
| `uint32`         | `w32`         |
| `uint16`         | `w16`         |
| `byte`           | `w8`          |
| `bool`           | `bool`        |
| `string`         | `go_string`   |
| `*T`             | `loc`         |
| `[]T`            | `slice.t`     |
| `func(x A) B`    | `func.t`      |
| `interface{...}` | `interface.t` |
| `any`            | `interface.t` |

```rocq
From sys_verif.program_proof Require Import prelude empty_ffi.
From sys_verif.program_proof Require Import heap_init.

Section proof.
Context `{hG: !heapGS Σ}.
Context `{!globalsGS Σ} {go_ctx: GoContext}.

```

Let's see those `IntoVal` instances in use.

```rocq
Definition int_to_val (x: w64): val := to_val x.
Definition int_to_val_notation (x: w64): val := #x.

(* these even print the same *)
Lemma notation_is_to_val (x: w64) : #x = to_val x.
Proof. reflexivity. Qed.

```

Points-to assertions always bake in the `IntoVal`, so you don't write `l ↦ #x` but just `l ↦ x`. Let's confirm the type signature, which requires first knowing what the notation expands to:

```rocq
Locate "↦".
```

:::: note Output

```txt
Notation "l ↦ dq v" := (typed_pointsto l dq v) : bi_scope
Notation "'[∨' 'list]' k ↦ x ∈ l , P" := (big_opL bi_or (fun k x => P) l)
  : bi_scope
Notation "'[∧' 'map]' k ↦ x ∈ m , P" := (big_opM bi_and (fun k x => P) m)
  : bi_scope
Notation "'[∧' 'list]' k ↦ x ∈ l , P" := (big_opL bi_and (fun k x => P) l)
  : bi_scope
Notation "'[∗' 'maps]' k ↦ x ; .. ; y ∈ ms , P" :=
  (big_sepMs ms (fun k x => .. (fun y => P) ..)) : bi_scope
Notation "'[∗' 'maplist]' k ↦ x ; v ∈ m ; l , P" :=
  (big_sepML (fun k x v => P) m l) : bi_scope
Notation "'[∗' 'map]' k ↦ x ∈ m , P" := (big_opM bi_sep (fun k x => P) m)
  : bi_scope
Notation "'[∗' 'map]' k ↦ x1 ; x2 ∈ m1 ; m2 , P" :=
  (big_sepM2 (fun k x1 x2 => P) m1 m2) : bi_scope
Notation "'[∗' 'list]' k ↦ x ∈ l , P" := (big_opL bi_sep (fun k x => P) l)
  : bi_scope
Notation "'[∗' 'list]' k ↦ x1 ; x2 ∈ l1 ; l2 , P" :=
  (big_sepL2 (fun k x1 x2 => P) l1 l2) : bi_scope
Notation "'[^' o 'map]' k ↦ x ∈ m , P" := (big_opM o (fun k x => P) m)
  : stdpp_scope (default interpretation)
Notation "'[^' o 'list]' k ↦ x ∈ l , P" := (big_opL o (fun k x => P) l)
  : stdpp_scope (default interpretation)
```

::::

```rocq
About typed_pointsto.
```

:::: note Output

```txt
typed_pointsto :
∀ {ext : ffi_syntax} {ffi : ffi_model} {ffi_interp0 : ffi_interp ffi}
  {Σ : gFunctors},
  heapGS Σ → ∀ {V : Type}, IntoVal V → loc → dfrac → V → iProp Σ

typed_pointsto is not universe polymorphic
Arguments typed_pointsto {ext ffi ffi_interp0 Σ heapGS0}
  {V}%type_scope {IntoVal0} l dq%dfrac_scope v
typed_pointsto is transparent
Expands to: Constant New.golang.theory.typed_pointsto.typed_pointsto
Declared in
library New.golang.theory.typed_pointsto, line 19, characters 13-27
```

::::

You can see that typed_pointsto takes a `V` and an argument `IntoVal V`. This is how typeclasses show up in signatures: an instance is passed as an argument. The key to making them work is that you'll actually write `typed_pointsto l dq v`, and Rocq will infer the `V` and `IntoVal V` arguments. You can imagine how `V` is inferred (its the type of `v`). Rocq looks for an instance of `IntoVal V` automatically - this search process is the main component in the implementation of typeclasses.

```rocq
Definition a_points_to (l: loc) (x: w64): iProp _ := l ↦ x.
Definition self_points_to (l: loc) : iProp _ := l ↦ l.

```

## Supporting struct values

Goose has more sophisticated support for structs. We want to have a nice user interface for structs, so Goose does some work to support a new Rocq `Record` for each struct defined in the Go code (technically, for every _defined type_ that wraps a struct, like `type Foo struct { ... }`, which is the most common way to use structs). These records are produced automatically in the generatedproof files by a tool called `proofgen` that ships with goose; this has all been run for you in this repo so you don't directly interact with it.

Let's see how this works with a concrete example, the `Person` struct defined in `go/heap/struct.go`. The Rocq record corresponding to `Person` is accessible as `heap.Person.t`, since `heap` is the Go package it came from:

```rocq
Print heap.Person.t.
```

:::: note Output

```txt
Record t : Type := mk
  { FirstName' : go_string;  LastName' : go_string;  Age' : w64 }.

Arguments heap.Person.mk (FirstName' LastName')%byte_string_scope Age'
Arguments heap.Person.FirstName' t
Arguments heap.Person.LastName' t
Arguments heap.Person.Age' t
```

::::

The fields of this record match the Go struct, with an extra prime `'` to avoid conflicts with other names. We can construct a value of this record using `heap.Person.mk`:

```rocq
Check heap.Person.mk "Ada" "Lovelace" (W64 25).
```

:::: note Output

```txt
{|
  heap.Person.FirstName' := "Ada";
  heap.Person.LastName' := "Lovelace";
  heap.Person.Age' := W64 25
|}
     : heap.Person.t
```

::::

Or we could construct values using Rocq's dedicated record syntax (which is how it will print the values back to you). This looks a bit painful, but you could use `Import heap` to make it shorter.

```rocq
Check {| heap.Person.FirstName' := "Ada";
         heap.Person.LastName' := "Lovelace";
         heap.Person.Age' := W64 25 |}.

```

proofgen gives us an `IntoVal heap.Person.t` instance, which we can use to state a points-to for a whole struct:

```rocq
Lemma wp_ExamplePersonRef :
  {{{ is_pkg_init heap.heap }}}
    @! heap.ExamplePersonRef #()
  {{{ (l: loc), RET #l;
      l ↦ (heap.Person.mk "Ada" "Lovelace" (W64 25)) }}}.
Proof.
  wp_start as "_".
  wp_alloc l as "p".
  wp_finish.
Qed.

```

We can split a points-to for a struct into its component fields. This is also implemented by proofgen, which implements the `StructFieldsSplit` typeclass. That class is more complicated because it's not a function but in fact a proof about the struct points-to.

```rocq
Lemma wp_ExamplePersonRef_fields :
  {{{ is_pkg_init heap.heap }}}
    @! heap.ExamplePersonRef #()
  {{{ (l: loc), RET #l;
      l ↦s[heap.Person :: "FirstName"] "Ada"%go ∗
      l ↦s[heap.Person :: "LastName"] "Lovelace"%go ∗
      l ↦s[heap.Person :: "Age"] W64 25
  }}}.
Proof.
  wp_start as "#init".
  wp_alloc l as "p".
  iApply struct_fields_split in "p".
  (* the output of `struct_fields_split` can be simplified by splitting it with `iNamed` and with `cbn` (or `simpl`). *)
  iNamed "p".
  cbn [heap.Person.FirstName' heap.Person.LastName' heap.Person.Age'].
  wp_finish.
Qed.

```

## Methods on structs

When we state a wp spec for a method (as opposed to a function), we have to say what type the method is for to be unambigious. This is the same information that goes into the Go type signature, just written in a different way. Here we need to reference not the Go type, but its "identifier", a unique name for it. Here's an example of stating such a lemma, where the receiver is a `Person` value (not a pointer). Notice that the type identifier provided is `heap.Person.id`.

```rocq
Lemma wp_Person__Name (firstName lastName: go_string) (age: w64) :
  {{{ is_pkg_init heap.heap }}}
  (heap.Person.mk firstName lastName age) @ heap.Person.id @ "Name" #()
  {{{ RET #(firstName ++ " " ++ lastName)%go; True }}}.
Proof.
  wp_start as "#init".
  (* wp_pures will automatically handle these field reference calculations, which compute pointers to the struct fields (at this point the method receiver is behind a pointer because all method arguments are stored on the heap to make them mutable). *)
  wp_alloc p_l as "p". wp_pures.
```

:::: info Goal diff

```txt
  firstName, lastName : go_string
  age : w64
  Φ : val → iPropI Σ
  p_l : loc
  ============================
  _ : is_pkg_init heap
  --------------------------------------□
  "HΦ" : True -∗ Φ (# (firstName ++ " "%go ++ lastName))
  "p" : p_l ↦ {|
                heap.Person.FirstName' := firstName;
                heap.Person.LastName' := lastName;
                heap.Person.Age' := age
              |}
  --------------------------------------∗
  WP exception_do
       (let: "p" := # p_l in // [!code --]
        return: ![# stringT] (struct.field_ref (# heap.Person) // [!code --]
                                (# "FirstName"%go) "p") + // [!code --]
       (return: ![# stringT] (# // [!code ++]
                                (struct.field_ref_f heap.Person "FirstName" // [!code ++]
                                   p_l)) + // [!code ++]
                # " "%go +
                ![# stringT] (struct.field_ref (# heap.Person)
                                (# "LastName"%go) "p")) // [!code --]
                                (# "LastName"%go)  // [!code ++]
                                (# p_l))) // [!code ++]
  {{ v, Φ v }}
```

::::

```rocq
  iApply struct_fields_split in "p"; iNamed "p";
  cbn [heap.Person.FirstName' heap.Person.LastName' heap.Person.Age'].
  wp_auto.
  wp_finish.
  rewrite -app_assoc //.
Qed.

```

One more example of a method, this time on a pointer. Thus we need the receiver to be a `loc`, the precondition needs ownership over that pointer (specifically, to all the fields of a `Person` at that location), and finally the receiver type is `(ptrT.id heap.Person.id)` to represent a pointer to a `Person` struct.

```rocq
Lemma wp_Person__Older (firstName lastName: byte_string) (age: w64) (p: loc) (delta: w64) :
  {{{ is_pkg_init heap.heap ∗
      p ↦s[heap.Person :: "FirstName"] firstName ∗
      p ↦s[heap.Person :: "LastName"] lastName ∗
      p ↦s[heap.Person :: "Age"] age
  }}}
    p @ (ptrT.id heap.Person.id) @ "Older" #delta
  {{{ RET #();
      p ↦s[heap.Person :: "FirstName"] firstName ∗
      p ↦s[heap.Person :: "LastName"] lastName ∗
      (* we avoid overflow reasoning by saying the resulting integer is just
      [word.add age delta], which will wrap at 2^64  *)
      p ↦s[heap.Person :: "Age"] word.add age delta
  }}}.
Proof.
  wp_start as "(first & last & age)".
  wp_auto.
  wp_finish.
Qed.

```

```rocq
End proof.
```
