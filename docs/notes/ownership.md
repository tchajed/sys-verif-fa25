---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture-note
tags: literate
order: 12
shortTitle: "Ownership in Go"
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Ownership reasoning with Goose

> Follow these notes in Rocq at [src/sys_verif/notes/ownership.v](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/src/sys_verif/notes/ownership.v).

## Learning outcomes

1. Translate informal descriptions of ownership to separation logic specifications, and back.
2. Use the different slice permissions to specify functions.

---

## Motivation

Consider the following hypothetical functions (these are not actual Go APIs):

```go
// FileAppend writes data to the end of f
func FileAppend(f *os.File, data []byte)
```

```go
// NetworkSend sends data on the TCP connection c
//
// data is not safe to use after this function.
func NetworkSend(c *net.Conn, data []byte)
```

These two signatures are very similar, but the comments say different things about data. `FileAppend` doesn't mention anything about safety of using data, while `NetworkSend` specifically cautions not to use the input buffer afterward. What's going on here?

The answer is that these two functions have different _ownership_ disciplines for their input buffers, and these are expressed only through comments. The ownership of the slice becomes more concrete when we look at (hypothetical) separation logic specifications:

```rocq
Lemma wp_FileAppend f data_s bs bs' :
  {{{ file_data(f, bs) ∗ own_slice data_s bs' }}}
    FileAppend f data_s
  {{{ file_data(f, bs ++ bs') ∗ own_slice data_s bs' }}}.
```

```rocq
Lemma wp_NetworkSend c data_s bs bs' :
  {{{ conn_stream(c, bs) ∗ own_slice data_s bs' }}}
    NetworkSend c data_s
  {{{ conn_stream(c, bs ++ bs') }}}.
```

In these specifications, `file_data(f, bs)` is a _representation predicate_ that expresses that the file `f` contains bytes `bs`, while `conn_stream(c, bs)` expresses that the bytes `bs` have been sent on stream `c`. `own_slice data_s bs'` is how we state that the slice value `data_s` points to the data `bs'` (a list of bytes in this case).

What these functions might do differently and how this translates to these specifications is one mystery this lecture will aim to resolve.

The ideas of _ownership_ and _permissions_ are at play in all of these examples. In each example, the code doesn't tell us which piece of the code is allowed to read or write a data structure, but knowing these permission rules is important for writing correct code. Separation logic allows us to specify and prove the permission discipline for a function. The specification communicates the ownership discpline, the proof ensures that we follow our stated ownership, and the caller's proof ensures that they follow whatever rules our function requires to be correct.

**Terminology note:** The term _ownership_ in C++ and Rust refers specifically to the permission (and responsibility) to _destroy_ an object, which is not important in Go as a garbage collected language. In the separation logic context ownership and permissions are used a bit more interchangeably.

```rocq
From sys_verif.program_proof Require Import prelude empty_ffi.
From Coq Require Import Strings.String.
From sys_verif.program_proof Require Import heap_init.

Section goose.
Context `{hG: !heapGS Σ}.
Context `{!globalsGS Σ} {go_ctx: GoContext}.

```

## Typed points-to assertion

The most basic form of ownership in Goose is the points-to assertion, which expresses ownership over a single heap variable. As we saw previously, a GooseLang heap variable is also used to model local variables (and function arguments, which behave just like local variables), since these are also mutable locations. Thus the same proof principles are used for Go pointers as for these local variables.

The location in a points-to is always of type `loc`, which is the type of heap locations. Rather than using `val` (the GooseLang type for all values, including literals and structs) directly in the notation, though, the Rocq implementation takes a Gallina value, such as a `w64` (the type of 64-bit integers) or `bool`:

```rocq
Definition pointsto_example_1 (l: loc): iProp Σ := l ↦ W64 1.
Definition pointsto_example_2 (l: loc): iProp Σ := l ↦ true.
Definition pointsto_example_3 (l: loc): iProp Σ := l ↦ l.

```

The points-to assertion can take any type `V` that implements a typeclass `IntoVal V`. Implementing this typeclass requires providing a function `to_val : V → val`. GooseLang already provides implementations for all the base literals, which is why the examples above work.

You'll see `IntoVal V` in another form in GooseLang code: `#x` is a notation for `to_val x`. Just like the points-to assertion, this allows using Gallina types in the GooseLang code.

A points-to assertion is required to load and store to a location. We think of the assertion both as permission to read and write to the location, as well as asserting what the current value is.

```rocq
Lemma wp_load_example (l: loc) :
  {{{ l ↦ W64 3 }}}
    let: "x" := ![#uint64T] #l in
    "x"
  {{{ RET #(W64 3); l ↦ W64 3 }}}.
Proof.
  wp_start as "l".
  wp_load.
  wp_auto.
  wp_finish.
Qed.

```

The code in this example includes a type annotation on the load, with the type `#uint64T`. This type is required since this load is not a core primitive, but instead a function. Composite values like structs are not stored in one heap location, but laid out with one field per location, and `![#s] #l` with a struct type `s` would load the fields individually. However, this specification hides that complexity: as long as the type `uint64T` matches the type of data in the points-to assertin (`w64`), we get the expected specification for loads.

## Read-only ownership: fractional permissions {#read-only}

Fractional permissions are an approach to reasoning about read-only access in separation logic.

This concept is explained as part of the Program Proofs guide in [fractional permissions](./program-proofs/fractions.md).

## Modeling Structs

Ownership over pointers to structs is more interesting than ownership over plain variables.

Here's an example of a Go struct and some methods on it, to illustrate the principles:

```go
type Person struct {
	FirstName string
	LastName  string
	Age       uint64
}

func (p Person) Name() string {
	return p.FirstName + " " + p.LastName
}

func (p *Person) Older(delta uint64) {
	p.Age += delta
}

func (p *Person) GetAge() *uint64 {
	return &p.Age
}

func ExamplePerson() Person {
	return Person{
		FirstName: "Ada",
		LastName:  "Lovelace",
		Age:       25,
	}
}
```

Goose models the struct as a tuple, but it hides this fact behind a nicer interface to treat the struct as a Rocq record. It generates a Rocq record called `Person.t` to model the data in a Go `Person` struct:

```rocq
Module Person.
Record t := mk {
  FirstName' : go_string;
  LastName' : go_string;
  Age' : w64;
}.
End Person.
```

A Rocq Record is essentially an inductive type with one constructor (called `Person.mk` in this case), but this command also generates functions for each field (for example, `Person.FirstName'`) to get one field from a `Person.t` record. Goose relates these Gallina fields to the GooseLang model of field references.

Next, we need to model structs in memory. We might be tempted to say a pointer to a struct is a location, and we store the tuple at that location in the heap. The code `p.Older(delta)` above could be translated to something like `p <- (FirstName p, (LastName p, Age p + delta))` - notice that this method takes a struct _pointer_ and not a _value_ in Go, and this is reflected in how we use `p` in the model.

The third method, `GetAge`, however, would be problematic for this model. What pointer should it return? We know what should happen if we read and write to that pointer, but don't have a value to return for just `GetAge`.

The solution Goose uses is not to store a struct in a single heap cell, but instead _one per field_. The heap locations are all laid out contiguously, just like an array. Thus the model for `GetAge` is actually `GetAge := λ: "ℓ", "ℓ" +ₗ 2`, where 2 is the index of the `Age` field.

The translated code for struct operations doesn't directly use offsets but instead uses a helper function `struct.field_ref` to compute the offset from a struct type and field name. We can see this used throughout the model in the translation of the code above:

```rocq
Definition Person : go_type := structT [
  "FirstName" :: stringT;
  "LastName" :: stringT;
  "Age" :: uint64T
].

Definition Person__Nameⁱᵐᵖˡ : val :=
  λ: "p" <>,
    exception_do (let: "p" := (mem.alloc "p") in
    return: (((![#stringT] (struct.field_ref #Person #"FirstName"%go "p")) + #" "%go) + (![#stringT] (struct.field_ref #Person #"LastName"%go "p")))).

Definition Person__Olderⁱᵐᵖˡ : val :=
  λ: "p" "delta",
    exception_do (let: "p" := (mem.alloc "p") in
    let: "delta" := (mem.alloc "delta") in
    do:  ((struct.field_ref #Person #"Age"%go (![#ptrT] "p")) <-[#uint64T] ((![#uint64T] (struct.field_ref #Person #"Age"%go (![#ptrT] "p"))) + (![#uint64T] "delta")));;;
    return: #()).

Definition Person__GetAgeⁱᵐᵖˡ : val :=
  λ: "p" <>,
    exception_do (let: "p" := (mem.alloc "p") in
    return: (struct.field_ref #Person #"Age"%go (![#ptrT] "p"))).

(* go: struct.go:21:6 *)
Definition ExamplePersonⁱᵐᵖˡ : val :=
  λ: <>,
    exception_do (return: (let: "$FirstName" := #"Ada"%go in
     let: "$LastName" := #"Lovelace"%go in
     let: "$Age" := #(W64 25) in
     struct.make #Person [{
       "FirstName" ::= "$FirstName";
       "LastName" ::= "$LastName";
       "Age" ::= "$Age"
     }])).
```

The first thing to notice is that even the struct `Person` is translated. It doesn't produce a GooseLang expression, but instead a `go_type`, which records the fields and their types in a list - we'll come back to those types later, which are most important when we have nested structs. This declaration is later used by the _Gallina_ function `struct.field_ref` to figure out what offset the fields have.

The easiest model to understand is `GetAge`, which is entirely based on the function `struct.field_ref`. The implementation searches the `Person` declaration for the field `Age` and returns a GooseLang function that takes the right offset from the input location, 2 in this case. We prove that the GooseLang function `struct.field_ref` computes a Gallina function `struct.field_ref_f` (you'll see that show up in proofs).

Similarly, `struct.make` takes a struct declaration and a list of field values and assembles them into a struct value, a tuple with all the fields. This is needed since a struct literal in Go need not be in the same order as the declaration (what would go wrong if we assumed it was?) and because fields can be omitted, in which case they get the zero value for their type. The declaration records both the order of the fields and the types for this reason.

## Ownership of structs

Goose has two key ideas for reasoning about structs: first, the typed points-to assertion allows ownership over structs, not just base data, and second, a points-to with a struct value is actually a separating conjunction of all of its fields.

To see these ideas in action, let's start with a function that doesn't involve ownership:

```rocq
Lemma wp_ExamplePerson :
  {{{ is_pkg_init heap.heap }}}
    @! heap.ExamplePerson #()
  {{{ RET #(heap.Person.mk "Ada" "Lovelace" (W64 25)); True }}}.
Proof.
  wp_start.
  wp_finish.
Qed.

```

`ExamplePerson` returns a struct value. We write the specification using Person.t, and use `#` to turn it into the GooseLang value that is actually returned (which is a tuple, not the Gallina record). The next example illustrates ownership over a struct pointer. It's helpful to see this in a context where `*Person` initially gets allocated. For that we'll use this function:

```go
func ExamplePersonRef() *Person {
	return &Person{
		FirstName: "Ada",
		LastName:  "Lovelace",
		Age:       25,
	}
}
```

This specification shows that the typed points-to can be used for something other than a base literal. The underlying mechanism is the `IntoVal` typeclass, used for both `#` and `l ↦ v`.

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

As discussed above, a Person struct in memory is not stored in a single location. The points-to above is actually a separating conjunction over three smaller points-to assertions, one for each field. We can break it down into _struct field points-to_ assertions of the form `l ↦s[heap.Person :: "Age"] (W64 25)`. This is actually notation for a simpler concept: `(struct.field_ref_f heap.Person "Age" l) ↦ (W64 25)`. That is, owning a struct field is simply owning an appropriate offset from the base pointer, computed based on the struct and field name.

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
  iApply struct_fields_split in "p". iNamed "p".
  cbn [heap.Person.FirstName' heap.Person.LastName' heap.Person.Age'].

```

The theorem `struct_fields_split` gives a way to take any points-to assertion with a struct type and split it into its component field points-to assertions, which is what the postcondition of this spec gives.

```rocq
  wp_finish.
Qed.

```

The two concepts of a single points-to for the whole struct and individual field points-to assertions are the main ideas for how Goose handles ownership of struct. We see them used throughout the rest of the examples above:

```rocq
Lemma wp_Person__Name (firstName lastName: go_string) (age: w64) :
  {{{ is_pkg_init heap.heap }}}
  (heap.Person.mk firstName lastName age) @ heap.Person.id @ "Name" #()
  {{{ RET #(firstName ++ " " ++ lastName)%go; True }}}.
Proof.
  wp_start as "#init".
```

Notice how the following `wp_pures` call transforms `struct.field_ref` into `#(struct.field_ref_f ...)` - this is from a Goose-provided theorem that relates the GooseLang code to a Gallina function.

```rocq
  wp_alloc p_l as "p". wp_pures.
```

:::: info Goal diff

```txt
  Σ : gFunctors
  hG : heapGS Σ
  globalsGS0 : globalsGS Σ
  go_ctx : GoContext
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

The `struct_fields_split` theorem turns a pointer to a struct into pointers for its individual fields.

```rocq
  iApply struct_fields_split in "p"; iNamed "p";
  cbn [heap.Person.FirstName' heap.Person.LastName' heap.Person.Age'].
```

:::: info Goal diff

```txt
  Σ : gFunctors
  hG : heapGS Σ
  globalsGS0 : globalsGS Σ
  go_ctx : GoContext
  firstName, lastName : go_string
  age : w64
  Φ : val → iPropI Σ
  p_l : loc
  ============================
  _ : is_pkg_init heap
  --------------------------------------□
  "HΦ" : True -∗ Φ (# (firstName ++ " "%go ++ lastName))
  "p" : p_l ↦ {| // [!code --]
                heap.Person.FirstName' := firstName; // [!code --]
                heap.Person.LastName' := lastName; // [!code --]
                heap.Person.Age' := age // [!code --]
              |} // [!code --]
  "HFirstName" : p_l ↦s[heap.Person :: "FirstName"] firstName // [!code ++]
  "HLastName" : p_l ↦s[heap.Person :: "LastName"] lastName // [!code ++]
  "HAge" : p_l ↦s[heap.Person :: "Age"] age // [!code ++]
  --------------------------------------∗
  WP exception_do
       (return: ![# stringT] (#
                                (struct.field_ref_f heap.Person "FirstName"
                                   p_l)) +
                # " "%go +
                ![# stringT] (struct.field_ref (# heap.Person)
                                (# "LastName"%go)
                                (# p_l)))
  {{ v, Φ v }}
```

::::

```rocq
  wp_auto.
  wp_finish.
  rewrite -app_assoc //.
Qed.

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

Here is one possible spec for `GetAge`, which results in breaking off the age field into its points-to assertion. Note that this spec allows the caller to retain ownership over the other fields, as opposed to a spec which only gave `age_l ↦ age` in the postcondition.

```rocq
Lemma wp_GetAge (firstName lastName: byte_string) (age: w64) (p: loc) (delta: w64) :
  {{{ is_pkg_init heap.heap ∗
      "first" :: p ↦s[heap.Person :: "FirstName"] firstName ∗
      "last" :: p ↦s[heap.Person :: "LastName"] lastName ∗
      "age" :: p ↦s[heap.Person :: "Age"] age
  }}}
    p @ (ptrT.id heap.Person.id) @ "GetAge" #()
  {{{ (age_l: loc), RET #age_l;
      p ↦s[heap.Person :: "FirstName"] firstName ∗
      p ↦s[heap.Person :: "LastName"] lastName ∗
      age_l ↦ age
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto.
  wp_finish.
Qed.

```

## Exercises: struct specifications

Fill in a specification for each function, then do the proof. Proofs should mostly be automated (using tactics like `wp_start`, `wp_auto`, and `wp_finish`) if you have a correct specification.

You'll need to reference the implementation of these functions and methods in [go/heap/struct.go](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/go/heap/struct.go).

```rocq
Lemma wp_Rect__Area (r_ptr0: loc) :
  {{{ is_pkg_init heap ∗ r_ptr0 ↦ () }}}
    r_ptr0 @ (ptrT.id heap.Rect.id) @ "Area" #()
  {{{ RET #(); True }}}.
Proof.
Admitted.

Lemma wp_IsSquare (r: heap.Rect.t) :
  {{{ True }}}
    @! heap.IsSquare #r
  {{{ RET #(); True }}}.
Proof.
Abort.

```

Use struct field points-tos for the pre- and post-condition in this specification.

```rocq
Lemma wp_Rect__MakeSquare (r_ptr0: loc) (width height: w64) :
  {{{ is_pkg_init heap }}}
    r_ptr0 @ (ptrT.id heap.Rect.id) @ "MakeSquare" #()
  {{{ RET #(); True }}}.
Proof.
Abort.

```

Note that this specification isn't stated for the correct function - you should fix that.

```rocq
Lemma wp_Rotate (r_ptr0: loc) (width height: w64) :
  {{{ is_pkg_init heap }}}
    Skip
  {{{ RET #(); True }}}.
Proof.
Abort.

```

This one is a bit subtle. First, figure out what's wrong with the code. Then, write an appropriate specification.

```rocq
Lemma wp_Person__BuggySetAge (p: unit) :
  {{{ True }}}
    p @ heap.Person.id @ "BuggySetAge" #()
  {{{ RET #(); True }}}.
Proof.
Admitted.

```

## Slices

Go has a slice type `[]T`, a generic type that works for any element type `T`.

### What are slices?

Slices in Go are implemented as a struct value with a pointer, a length, and a capacity; this is also how they are modeled in GooseLang. It is helpful to know some implementation details to understand how they work. This structure of pointer, length, and capacity is a common pattern for dynamically sized arrays (e.g., C++'s `std::vector` and Rust's `Vec` are almost identical).

You can read more about Go slices in this post on [Go data structures](https://research.swtch.com/godata) or in even more detail in this [post on slices and append](https://go.dev/blog/slices).

More primitive than slices is the idea of an _array_. An array is a contiguous block of memory, and we interact with them through a pointer to the first element. A slice is a "view" into a piece of an array (possibly the entire thing, but not necessarily). You can think of a slice as containing (at any given time) a sequence of elements. The slice is a (pointer, length, capacity) tuple, where the pointer points to the first element in the slice and the length says how many elements are in the slice. The array in memory is contiguous, so we can find any element by taking an offset from the pointer. Finally, the capacity tracks elements past the length that are allocated and in the array, which is memory available to grow the slice if elements are appended.

Remember that there is a difference between a slice _value_ (the tuple of pointer, length, capacity) and what it points to (a sequence of elements in memory), much like the difference between a pointer _value_ (a memory address) and whatever it points _to_.

The Go `append(s, x)` operation appends to a slice and returns a new slice. If `s` has spare capacity, the new element is stored there and the new slice has the same pointer as the old one, but with its length increased by 1. On the other hand if `s` has no spare capacity, `append` allocates a new, larger array and copies the elements pointed to by `s` over to it. When a slice is grown, typically its capacity will be double the original length, to amortize the cost of copying over the elements; hopefully you saw something like this in a data structure class (it's often the first example shown of amortized cost analysis). A common idiom for appending to a slice `s []T` is `s = append(s, x)`, since we typically want to only use the new slice.

### Reasoning about slices

The basic assertion for working with slices is `own_slice s dq xs`. `s` is a `Slice.t`, a Rocq record representing the slice value (the triple of pointer, length, and capacity); GooseLang code will use `#s`, the standard way of converting Gallina values to GooseLang values. `dq` is a fraction, explained below; for now we will pretend like it's always `DfracOwn 1`. Finally, `xs` is a Gallina `list V` of the elements of the slice, with the same flexibility for the type `V` as used in points-to assertions, namely `V` can be any type that satisfies `IntoVal V`. The overall result is an assertion that gives ownership over the memory referenced by the slice `s`, and records that it has the elements `xs`.

This abstraction uses typeclasses so the type of `xs` can vary, so for example we can use `list w64` for a slice of integers. You can see this in the type signature for `own_slice`, where there are parameters `V: Type` and `IntoVal V`:

```rocq
About own_slice.
```

:::: note Output

```txt
own_slice :
∀ {H : ffi_syntax} {ffi : ffi_model} {H0 : ffi_interp ffi} {Σ : gFunctors},
  heapGS Σ
  → ∀ {V : Type} {IntoVal0 : IntoVal V} {t : go_type},
      IntoValTyped V t → slice.t → dfrac → list V → iProp Σ

own_slice is not universe polymorphic
Arguments own_slice {H ffi H0 Σ heapGS0} {V}%type_scope
  {IntoVal0 t IntoValTyped0} s dq%dfrac_scope vs%list_scope
own_slice is transparent
Expands to: Constant New.golang.theory.slice.own_slice
Declared in library New.golang.theory.slice, line 35, characters 19-28
```

::::

You can ignore this whole string of parameters, which are related to Goose support for interacting with disks and the network (all of the "external" and "FFI" related parameters):

```rocq
{ext : ffi_syntax} {ffi : ffi_model} {ffi_interp0 : ffi_interp ffi}
  {Σ : gFunctors},
  heapGS Σ
  → ∀ {ext_ty : ext_types ext}
```

GooseLang models loading and storing slice elements in a similar way to struct field operations: a GooseLang function `slice.elem_ref` computes a pointer to the relevant element (the analogous Gallina function is `slice.elem_ref_f`), and then that element pointer can be used like any other pointer. We can see that in these two specifications:

```rocq
Check wp_load_slice_elem.
```

:::: note Output

```txt
wp_load_slice_elem
     : ∀ (s : slice.t) (i : w64) (vs : list ?V) (dq : dfrac) (v : ?V),
         0 ≤ sint.Z i
         → {{{ s ↦*{dq} vs ∗ ⌜vs !! sint.nat i = Some v⌝ }}}
             ![# ?t] (# (slice.elem_ref_f s ?t i))
           {{{ RET # v; s ↦*{dq} vs }}}
where
?V :
  [Σ : gFunctors  hG : heapGS Σ  globalsGS0 : globalsGS Σ  go_ctx : GoContext
  |- Type]
?IntoVal0 :
  [Σ : gFunctors  hG : heapGS Σ  globalsGS0 : globalsGS Σ  go_ctx : GoContext
  |- IntoVal ?V]
?t :
  [Σ : gFunctors  hG : heapGS Σ  globalsGS0 : globalsGS Σ  go_ctx : GoContext
  |- go_type]
?IntoValTyped0 :
  [Σ : gFunctors  hG : heapGS Σ  globalsGS0 : globalsGS Σ  go_ctx : GoContext
  |- IntoValTyped ?V ?t]
```

::::

We got this specification using `Check` rather than copying it from the Perennial source code.

One complication in using this specification is that its precondition requires the caller to pass the value `v0` that is in the slice. This automatically enforces that the index is less than the length of the slice, that is, `sint.nat i < length vs` (we separately need the index to be non-negative, hence the precondition `0 ≤ sint.Z i`).

Storing is fairly similar:

```rocq
Check wp_store_slice_elem.
```

:::: note Output

```txt
wp_store_slice_elem
     : ∀ (s : slice.t) (i : w64) (vs : list ?V) (v' : ?V)
         (Φ : val → iPropI Σ),
         s ↦* vs ∗ ⌜0 ≤ sint.Z i < length vs⌝ -∗
         ▷ (s ↦* <[sint.nat i:=v']> vs -∗ Φ (# ())) -∗
         WP # (slice.elem_ref_f s ?t i) <-[# ?t] # v' {{ v, Φ v }}
where
?V :
  [Σ : gFunctors  hG : heapGS Σ  globalsGS0 : globalsGS Σ  go_ctx : GoContext
  |- Type]
?IntoVal0 :
  [Σ : gFunctors  hG : heapGS Σ  globalsGS0 : globalsGS Σ  go_ctx : GoContext
  |- IntoVal ?V]
?t :
  [Σ : gFunctors  hG : heapGS Σ  globalsGS0 : globalsGS Σ  go_ctx : GoContext
  |- go_type]
?IntoValTyped0 :
  [Σ : gFunctors  hG : heapGS Σ  globalsGS0 : globalsGS Σ  go_ctx : GoContext
  |- IntoValTyped ?V ?t]
```

::::

All slice operations, including getting an element reference and subslicing, require that all indices be in bounds: when something is out of bounds, the Go code panics, and we model that panic as something unsafe which proofs must prove never occurs (remember that a separation logic triple proves that the code being verified is "safe" if the precondition holds).

In order to prove properties about bounds, we need to reason about the length of a slice. The slice value `(s: slice.t)` has a length field `slice.len_f s`. However, we typically have `s ↦* xs` and would rather reason about the length of the high-level list `xs` rather than explicitly reason about the length field of the slice. These two are related by the `own_slice_len` lemma, so it's typical to use that lemma at the beginning of a proof with something like `iDestruct (own_slice_len with "Hs") as %Hlen`, if `"Hs" : s ↦* xs` is a spatial hypothesis with a slice. Subsequently we will be able to use the `word` tactic to prove something is less than `slice.len_f s`, which will automatically take advantage of this hypothesis.

::: tip Slice lemmas

You should read the proof below to see everything we talk about above in practice, in the context of a real proof.

:::

This slightly complicated proof illustrates both the load and store specs above as well as how to do the arithmetic reasoning required.

The code being verified is a one-liner:

```go
func SliceSwap(s []int, i, j int) {
	s[i], s[j] = s[j], s[i]
}
```

```rocq
Lemma wp_SliceSwap (s: slice.t) (xs: list w64) (i j: w64) (x_i x_j: w64) :
  {{{ is_pkg_init heap.heap ∗ s ↦* xs ∗ ⌜xs !! sint.nat i = Some x_i ∧ xs !! sint.nat j = Some x_j⌝ ∗ ⌜0 ≤ sint.Z i ∧ 0 ≤ sint.Z j⌝ }}}
    @! heap.SliceSwap #s #i #j
  {{{ RET #(); s ↦* <[ sint.nat j := x_i ]> (<[ sint.nat i := x_j ]> xs) }}}.
Proof.
  wp_start as "(Hs & [%Hi %Hj] & %Hbound)".
  wp_auto.

  (* The slice specs require a bit of boilerplate to prove all the in-bounds requirements. *)
  pose proof Hi as Hi_bound.
  apply lookup_lt_Some in Hi_bound.
  pose proof Hj as Hj_bound.
  apply lookup_lt_Some in Hj_bound.


```

Most proofs involving slices require you to use this lemma to relate the slice length (the field of the slice value `s`) to the length of the list in the `own_slice` predicate (the assertion `s ↦* xs`)

```rocq
  iDestruct (own_slice_len with "Hs") as %Hlen.


```

`slice.elem_ref` requires calling `wp_pure` and then proving that the indices are in-bounds, since Go panics even if you just compute these indices

```rocq
  wp_pure.
  { word. }
  wp_apply (wp_load_slice_elem with "[$Hs]") as "Hs".
  { word. }
  { eauto. }

  wp_pure; first word.
  wp_apply (wp_load_slice_elem with "[$Hs]") as "Hs"; first word.
  { eauto. }

  wp_pure; first word.
  wp_apply (wp_store_slice_elem with "[$Hs]") as "Hs"; first word.

  wp_pure; first word.
  wp_apply (wp_store_slice_elem with "[$Hs]") as "Hs".
  { autorewrite with len. word. }

  wp_finish.
Qed.

```

Storing into a slice requires only a proof that the index is in-bounds. The postcondition uses `<[sint.nat i := v]> vs` which is a Gallina implementation of updating one index of a list (it's notation for the function `insert` from std++).

You may notice that there's an arbitrary `q : dfrac` in the specification for `wp_load_slice_elem`, while `wp_store_slice_elem` does not have a fraction (it is implicitly 1). This is analogous to the read-only ownership for plain pointers that we saw earlier.

### Appending to a slice

The ownership reasoning for appending to a slice turns out to be especially interesting in Go. The way this shows up is that it turns out that owning the logical _elements_ of a slice (the memory for `s.(slice.len_f)` elements, starting from the base pointer of the slice) is separate from the ownership of the _capacity_ (the memory from the length up to the capacity).

Consider the following code, which splits a slice:

```go
s := []int{1,2,3}
s1 := s[:1]
s2 := s[1:]
```

What is not obvious in this example is that in Go, `s1` has a capacity that _overlaps_ with that of `s2`. Specifically, the behavior of this code is surprising (you can [run it yourself](https://go.dev/play/p/yhcjYdVBVjo) on the Go playground):

```go
s := []int{1,2,3}
s1 := s[:1]
s2 := s[1:]
fmt.Println(s2[0]) // prints 2
s1 = append(s1, 5)
fmt.Println(s2[0]) // prints 5, not 2!
```

Goose accurately models this situation. If `s = (ptr, l, c)`, we know from construction that `l = 3` and `c ≥ 3`. The key to modeling the rest of the code is that `s[:1] = (ptr, 1, c)` (with a capacity that includes the original allocation) while `s[1:] = (ptr + 1, 2, c-2)`. The append to `s1 = s[:1]` writes to the same memory occupied by `s2[0]`.

In proofs, Goose separates out the predicates for ownership of a slice's elements (between 0 and its length) and its capacity (from length to capacity).

- `own_slice s dq xs` asserts ownership only over the elements within the length of `s`, and says they have values `(xs: list V)`.
- `own_slice_cap V s dq` asserts ownership over just the capacity of `s`, saying nothing about their contents. It takes the Gallina type of elements `V`. This ownership may be fractional, though it is typically 1.
- `own_slice s dq xs ∗ own_slice_cap V s (DfracOwn 1)` asserts ownership over the elements and capacity of slice `s`.

These predicates are just definitions that are separating conjunctions over regular points-to facts for the elements. In the context of the example above, with `s = (ptr, 3, 4)` (notice we picked a capacity of 4), these predicates are equal to the following:

- `own_slice s [1;2;3] = (ptr + 0) ↦ 1 ∗ (ptr + 1) ↦ 2 ∗ (ptr + 2) ↦ 3`
- `own_slice_cap s [1;2;3] = ∃ x, (ptr + 3) ↦ x`
- ```
  own_slice (s[1:]) [2; 3]
   = ((ptr + 1) + 0) ↦ 2 ∗ ((ptr + 1) + 1) ↦ 3
   = (ptr + 1) ↦ 2 ∗ (ptr + 2) ↦ 3
  ```

Confirm for yourself that `own_slice` and `own_slice_cap` are disjoint; without that, we could never own both the slice and capacity.

The main specification related to capacity is the one for append:

```rocq
Lemma wp_slice_append (s: slice.t) (vs: list V) (s2: slice.t) (vs': list V) dq :
  {{{ s ↦* vs ∗ own_slice_cap V s (DfracOwn 1) ∗ s2 ↦*{dq} vs' }}}
    slice.append #t #s #s2
  {{{ (s': slice.t), RET #s';
      s' ↦* (vs ++ vs') ∗ own_slice_cap V s' (DfracOwn 1) ∗ s2 ↦*{dq} vs' }}}.
```

Notice that `own_slice_cap` appears in the pre-condition, with fraction 1; this is required since append will write to the elements in the capacity if there is room.

With this specification, we can now return to the example above. What is key to understanding the Go example above is that the Go expression `s[:n]` is ambiguous as to how it handles ownership. The capacity of `s[:n]` and `s[n:]` overlap; if we model `s[:n]` with `slice.slice_f s 0 n` and `s[n:]` as `slice.slice_f s n s.(slice.len_f)`, then there are two main choices for how to divide ownership when taking a prefix (taking some liberty to omit fractions and use n as both a w64 and a nat)

- `own_slice s xs ∗ own_slice_cap s V ⊢ own_slice (slice.slice_f s 0 n) (take xs n))`. Drop any ownership over the elements after `n`, but retain the capacity of the smaller slice.
- `own_slice s xs ⊢ own_slice (slice.slice_f s 0 n) (take xs n)) ∗ own_slice (slice.slice_f s n s.(slice.len_f) (drop xs n))`. Split ownership, but lose the ability to append to the prefix.

There is one more possibility which is a slight variation on splitting:

- `own_slice s xs ∗ own_slice_cap s V ⊢ own_slice (slice.slice_f s 0 n) (take xs n)) ∗ own_slice (slice.slice_f s n s.(slice.len_f)) (drop xs n)) ∗ own_slice_cap (slice.slice_f s n s.(slice.len_f))`. If we start out with ownership of the capacity, we can split ownership and still be able to append to the _second_ part (its capacity is the capacity of the original slice). We can actually derive this from the lower-level fact that `slice_cap s V ⊣⊢ slice_cap (slice.slice_f s n s.(slice.len_f)) V` if `n` is in-bounds.

### Exercise: find the theorems above in Perennial

Either using `Search` or by looking at the source code in Perennial, find the theorems above.

The relevant source code is the file `new/golang/theory/slice.v` in Perennial (you can use the submodule copy in your exercises repo).

### Exercise: attempt a proof outline for the append example

Try to use the predicates and rules for slice ownership to give a proof outline for the append example. At some point you will get stuck, because the reasoning principles don't give a way to verify the code above - this is fine in that we don't really intend to verify odd code like the above, but seeing exactly where you get stuck is instructive for learning how the rules work.

```rocq
End goose.
```
