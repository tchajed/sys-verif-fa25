---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture
tags: literate
order: 13
shortTitle: "Lecture 13: Ownership in Go"
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Lecture 13: Goose - Ownership reasoning

> Follow these notes in Coq at [src/sys_verif/program_proof/ownership.v](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/src/sys_verif/program_proof/ownership.v).

## Learning outcomes

1. Translate informal descriptions of ownership to separation logic specifications, and back.
2. Use the different slice permissions to specify functions.
3. Read and write specifications with fractional permissions.

Theme for today: ownership in Go and in GooseLang

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

```coq
Lemma wp_FileAppend f data_s bs bs' :
  {{{ file_data(f, bs) ∗ own_slice data_s bs' }}}
    FileAppend f data_s
  {{{ file_data(f, bs ++ bs') ∗ own_slice data_s bs' }}}.
```

```coq
Lemma wp_NetworkSend c data_s bs bs' :
  {{{ conn_stream(c, bs) ∗ own_slice data_s bs' }}}
    NetworkSend c data_s
  {{{ conn_stream(c, bs ++ bs') }}}.
```

What these functions might do differently and how this translates to these specifications is one mystery this lecture will aim to resolve.

The ideas of _ownership_ and _permissions_ are at play in all of these examples. In each example, the code doesn't tell us which piece of the code is allowed to read or write a data structure, but knowing these permission rules is important for writing correct code. Separation logic allows us to specify and prove the permission discipline for a function. The specification communicates the ownership discpline, the proof ensures that we follow our stated ownership, and the caller's proof ensures that they follow whatever rules our function requires to be correct.

**Terminology note:** The term _ownership_ in C++ and Rust refers specifically to the permission (and responsibility) to _destroy_ an object, which is not important in Go as a garbage collected language. In the separation logic context ownership and permissions are used a bit more interchangeably.

### Ownership in iterators

As another example, consider a hashmap with an iteration API that looks like this:

```go
func PrintKeys(m HashMap) {
  it := m.KeyIterator()
  for k, ok := it.Next(); ok {
      fmt.Println(k)
  }
}
```

That is, we have an API like this (where `Key` is a placeholder for the key type):

```go
// normal operations:
func (m HashMap) Get(k Key) (v Value, ok bool)
func (m HashMap) Put(k Key, v Value)
func (m HashMap) Delete(k Key)

// iteration:
func (m HashMap) KeyIterator() *Iterator
func (it *Iterator) Next() (k Key, ok bool)
```

Given this API, is this safe?

```go
// does this work?

func PrintValues(m HashMap) {
  it := m.KeyIterator()
  for k, ok := it.Next(); ok {
      v, _ := m.Get(k)
      fmt.Println(v)
  }
}
```

What about this one?

```go
// does this work?

func ClearMap(m HashMap) {
  it := m.KeyIterator()
  for k, ok := it.Next(); ok {
      m.Delete(k)
  }
}
```

::: details Solution

You can't tell from just the API (which does not even describe ownership in comments), but for most hashmap implementations this would not be safe - the problem is often called _iterator invalidation_ since the call to `m.Delete(k)` is considered to _invalidate_ `it` in the next iteration.

:::

## Structs

Go has structs. Here's an example, along with a few methods:

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

The ownership principle for structs can best be seen in `Older` and `GetAge`. Notice that `Older` only needs ownership (or permission to access) the field Age, not the entire struct `p *Person`. Similarly, `GetAge` is fundamentally about extracting ownership over the single field `p.Age`; different (but related) assertions are needed to give the ownership of `p` and of `&p.Age`.

Methods on structs are actually quite easy to model: `Name` becomes a function `Person__Name` that takes `p` as its first argument. The struct name is prepended to disambiguate this function from another function `Name` in the same scope (or another struct method called `Name`). Whenever Go calls a method on a struct, it is translated to a call to the appropriate function. If you're not sure how Go methods work as a language feature, read the [Go tour on methods](https://go.dev/tour/methods/1).

You might wonder if this is too simple. Go's methods are actually what is simple in this case: what complicates methods in object-oriented languages with inheritance like Java or C++ is that a call to a method might actually resolve to a superclass implementation, and in fact the exact method called might be dynamic. Go has `interface`s that behave somewhat similarly, which Goose does not model; interfaces are still simpler than inheritance and with some engineering Goose could support them without too much pain. (Inheritance could also be modeled but with a little more pain.)

Having handled methods, structs introduce two main challenges: how to model struct values, and how to model struct pointers.

Let's start with modeling struct values. The basic strategy is to translate a value of type `p: Person` to a tuple of the fields of the struct. To keep GooseLang simple, it only has binary pairs, not arbitrary-sized tuples, and functions `Fst` and `Snd` access the elements of a pair (these were called $\pi_1$ and $\pi_2$ way back in the `expr` language, but we'll use names for them now). With the tuple model, a person as in the `ExamplePerson()` function above would have the value `(#"Ada", (#"Lovelace", #(W64 25)))`.

To model field access, like `p.FirstName` that shows up in the `Name` method, we need to use `Fst` and `Snd` appropriately based on what index the field has; in this case it's easy and the model should be `Fst p`.

### Exercise: accessing other fields

:::: info Exercise

What's the right model of `p.LastName` and `p.Age`? Remember that we organized the tuple as `(#"Ada", (#"Lovelace", #(W64 25)))`.

::: details Solution

`p.LastName` should be modeled as `Fst (Snd p)` and `p.Age` is `Snd (Snd p)`.

:::

::::

### Struct pointers

We might be tempted to say a pointer to a struct is a location, and we store the tuple in the heap. The code `p.Older(delta)` above could be translated to something like `p <- (FirstName p, (LastName p, Age p + delta))` - notice that this method takes a struct _pointer_ and not a _value_ in Go, and this is reflected in how we use `p` in the model. This approach to translating structs is basically fine for this case (even if a bit complicated to implement), but it is limited.

The third method, `GetAge`, however, would be problematic for this model. What pointer should it return? We know what should happen if we read and write to that pointer, but don't have a value to return for just `GetAge`.

The solution Goose uses is not to use a single location for a struct, but instead _one per field_. The heap locations are all laid out contiguously, just like an array. Thus the model for `GetAge` is actually `GetAge := λ: "ℓ", "ℓ" +ₗ 2`, where 2 is the index of the `Age` field.

## Proofs using structs

Now let's see how this theory translates to Goose. First of all, we don't literally work with field offsets as literals; we would want constants based on the field names for those immediately in the proofs, and the actual translation uses field names in an even better way.

Here's the actual translation of the structs above:

```coq
Definition Person := struct.decl [
  "FirstName" :: stringT;
  "LastName" :: stringT;
  "Age" :: uint64T
].

Definition Person__Name: val :=
  rec: "Person__Name" "p" :=
    ((struct.loadF Person "FirstName" "p") +
    #(str" ")) +
    (struct.loadF Person "LastName" "p").

Definition Person__Older: val :=
  rec: "Person__Older" "p" "delta" :=
    struct.storeF Person "Age" "p"
                  ((struct.loadF Person "Age" "p") + "delta");;
    #().

Definition Person__GetAge: val :=
  rec: "Person__GetAge" "p" :=
    struct.fieldRef Person "Age" "p".

Definition ExamplePerson: val :=
  rec: "ExamplePerson" <> :=
    struct.mk Person [
      "FirstName" ::= #(str"Ada");
      "LastName" ::= #(str"Lovelace");
      "Age" ::= #25
    ].
```

The first thing to notice is that even the struct `Person` is translated. It doesn't produce a GooseLang expression, but instead a "struct declaration", which records the fields and their types in a list - we'll come back to those types later, which are most important when we have nested structs. This declaration is later used by _Gallina_ functions like `struct.loadF` and `struct.storeF` to figure out what offset the fields have.

The easiest model to understand is `GetAge`, which is entirely based on the Gallina function `struct.fieldRef`. The implementation searches the `Person` declaration for the field `Age` and returns a GooseLang function that takes the right offset from the input location, 2 in this case.

Similarly, `struct.mk` takes a struct declaration and a list of field values and assembles them into a struct value, a tuple with all the fields. This is needed since a struct literal in Go need not be in the same order as the declaration (what would go wrong if we assumed it was?) and because fields can be omitted, in which case they get the zero value for their type. The declaration records both the order of the fields and the types for this reason.

The other Gallina functions in this example, `struct.loadF` and `struct.storeF` are very similar to `struct.fieldRef`, except that they also do a store or load at the location.

Goose has a nice set of reasoning principles for structs, which extend the basic points-to assertion we've been using for heap locations. Let's see what specifications for the code above look like.

```coq
From sys_verif.program_proof Require Import prelude empty_ffi.
From Coq Require Import Strings.String.
From sys_verif.program_proof Require Import heap_init.

Section goose.
Context `{hG: !heapGS Σ}.
Context `{!goGlobalsGS Σ}.
Context `{!heap.GlobalAddrs}.

```

Goose does actually model struct values as tuples, and doesn't (yet) have a better way to write them in specs.

In practical use, we typically define a Gallina record and relate these records to the GooseLang representation, and then most specs work with the Gallina record and not with these tuples.

Notice also that there's an extra unit value at the end; this makes the recursive functions for accessing fields much simpler.

```coq
Lemma wp_ExamplePerson :
  {{{ is_pkg_init heap.heap }}}
    heap.heap @ "ExamplePerson" #()
  {{{ RET #(heap.Person.mk "Ada" "Lovelace" (W64 25)); True }}}.
Proof.
  wp_start as "_".
  iApply "HΦ".
  done.
Qed.

Lemma wp_Person__Name (firstName lastName: go_string) (age: w64) :
  {{{ is_pkg_init heap.heap }}}
    heap.Person__Name
      #(heap.Person.mk firstName lastName age) #()
  {{{ RET #(firstName ++ " " ++ lastName)%go; True }}}.
Proof.
  wp_start as "#init".
  wp_call.
  wp_alloc p_l as "p". wp_pures.
  iApply struct_fields_split in "p". iNamed "p".
  cbn [heap.Person.FirstName' heap.Person.LastName' heap.Person.Age'].
  wp_auto.
  iDestruct ("HΦ" with "[]") as "HΦ".
  { done. }
  iExactEq "HΦ".
  f_equal.
  f_equal.
  rewrite -app_assoc //.
Qed.

```

It's helpful to see the struct reasoning where `*Person` gets allocated before seeing how to use it. For that we'll use this function:

```go
func ExamplePersonRef() *Person {
	return &Person{
		FirstName: "Ada",
		LastName:  "Lovelace",
		Age:       25,
	}
}
```

The postcondition of the following spec introduces the _struct field points-to_. `l ↦s[heap.Person :: "Age"] (W64 25)` combines calculating an offset from `l` for the Age field of Person (that is, computing `l +ₗ #2`) with asserting that the value at that location is `#25`.

```coq
Lemma wp_ExamplePersonRef :
  {{{ is_pkg_init heap.heap }}}
    heap @ "ExamplePersonRef" #()
  {{{ (l: loc), RET #l;
      l ↦s[heap.Person :: "FirstName"] "Ada"%go ∗
      l ↦s[heap.Person :: "LastName"] "Lovelace"%go ∗
      l ↦s[heap.Person :: "Age"] W64 25
  }}}.
Proof.
  wp_start as "#init".
  wp_alloc l as "p".

```

Notice in the goal above how the struct allocation produced a `p ↦[struct.t heap.Person] v` assertion. This is actually the same as the points-to assertion we've been using all along, albeit with a more complex type. This assertion actually says that `v` is a tuple with the right structure to be a `Person` struct, and its three values are laid out in memory starting at `p`.

Now look at what the following line of proof does to the goal.

```coq
  iApply struct_fields_split in "p". iNamed "p".
  cbn [heap.Person.FirstName' heap.Person.LastName' heap.Person.Age'].

```

The theorem `struct_fields_split` gives a way to take any points-to assertion with a struct type and split it into its component field points-to assertions, which is what the postcondition of this spec gives.

```coq
  wp_pures.
  iApply "HΦ".
  iFrame.
Qed.

Lemma wp_Person__Older (firstName lastName: byte_string) (age: w64) (p: loc) (delta: w64) :
  {{{ is_pkg_init heap.heap ∗
      p ↦s[heap.Person :: "FirstName"] firstName ∗
      p ↦s[heap.Person :: "LastName"] lastName ∗
      p ↦s[heap.Person :: "Age"] age
  }}}
    p @ heap.heap @ "Person'ptr" @ "Older" #delta
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
  iApply "HΦ".
  iFrame.
Qed.

```

Here is one spec for `GetAge`, which results in breaking off the age field into its points-to assertion.

```coq
Lemma wp_GetAge (firstName lastName: byte_string) (age: w64) (p: loc) (delta: w64) :
  {{{ is_pkg_init heap.heap ∗
      "first" :: p ↦s[heap.Person :: "FirstName"] firstName ∗
      "last" :: p ↦s[heap.Person :: "LastName"] lastName ∗
      "age" :: p ↦s[heap.Person :: "Age"] age
  }}}
    p @ heap.heap @ "Person'ptr" @ "GetAge" #()
  {{{ (age_l: loc), RET #age_l;
      p ↦s[heap.Person :: "FirstName"] firstName ∗
      p ↦s[heap.Person :: "LastName"] lastName ∗
      age_l ↦ age
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto.
  (* this works pleasantly well, even with complicated struct references *)
  iApply "HΦ".
  iFrame.
Qed.

```

## Slices

Go has a slice type `[]T`, a generic type that works for any element type `T`.

### What are slices?

Slices in Go are implemented as a struct value with a pointer, a length, and a capacity; this is also how they are modeled in GooseLang. It is helpful to know this implementation detail to understand how they work, and it is also a common pattern for dynamically sized arrays (e.g., C++'s `std::vector` and Rust's `Vec` are almost identical).

You can read more about Rust slices in this post on [Go data structures](https://research.swtch.com/godata) or in even more detail in this [post on slices and append](https://go.dev/blog/slices). Below are some basic details.

More primitive than slices are arrays. An array is a contiguous block of memory, and we interact with them through a pointer to the first element. A slice is a "view" into a piece of an array (possibly the entire thing, but not necessarily). You can think of a slice as containing (at any given time) a sequence of elements. The slice is a (pointer, length, capacity) tuple, where the pointer points to the first element in the slice and the length says how many elements are in the slice. The array in memory is contiguous, so we can find any element by taking an offset from the pointer. Finally, the capacity tracks elements past the length that are allocated and in the array, which is memory available to grow the slice if elements are appended.

In Go, the common idiom for appending to a slice `s []T` is `s = append(s, x)`. This is because if `s` has no spare capacity, `append` allocates a new, larger array and copies the elements over to it; this cannot change `s` since this is passed by value, so instead the new slice is returned. When a slice is grown, typically its capacity will be double the original length, to amortize the cost of copying over the elements; hopefully you saw something like this in a data structure class, perhaps as the first example of an amortized analysis.

### Reasoning about slices

The basic assertion for working with slices is `own_slice s t dq xs`. `s` is a `Slice.t`, a Coq record representing the slice value (the triple of pointer, length, and capacity); in GooseLang code, you will instead use `slice_val s : val`. `t` is the type of elements, similar to the types used for structs and struct fields. `dq` is a fraction, explained below; for now we will pretend like it's always `DfracOwn 1`. Finally, `xs` is a Gallina `list` of the elements of the slice. The overall result is an assertion that gives ownership over the slice `s`, and records that it has the elements `xs`.

This abstraction uses typeclasses so the type of `xs` can vary, so for example we can use `list w64` for a slice of integers. You can see this in the type signature for `own_slice`, where there are parameters `V: Type` and `IntoVal V`:

```coq
About own_slice.
```

:::: note Output

```txt title="coq output"
own_slice :
∀ {H : ffi_syntax} {ffi : ffi_model} {H0 : ffi_interp ffi} {Σ : gFunctors},
  heapGS Σ
  → ∀ {V : Type} {IntoVal0 : IntoVal V} {t : go_type},
      IntoValTyped V t → slice.t → dfrac → list V → iProp Σ

own_slice is not universe polymorphic
Arguments own_slice {H ffi H0 Σ heapGS0} {V}%_type_scope
  {IntoVal0 t IntoValTyped0} s dq vs%_list_scope
own_slice is transparent
Expands to: Constant New.golang.theory.slice.own_slice
Declared in library New.golang.theory.slice, line 34, characters 19-28
```

::::

You can ignore this whole string of parameters, which are related to Goose support for interacting with disks and the network (all of the "external" and "FFI" related parameters):

```coq
{ext : ffi_syntax} {ffi : ffi_model} {ffi_interp0 : ffi_interp ffi}
  {Σ : gFunctors},
  heapGS Σ
  → ∀ {ext_ty : ext_types ext}
```

Getting and setting slice elements have reasonable specifications:

TODO: fix the written explanation in this lecture: slice operations are now based on getting a reference and using it, not `SliceGet` and `SliceSet`

```coq
Check wp_load_slice_elem.
```

:::: note Output

```txt title="coq output"
wp_load_slice_elem
     : ∀ (s : slice.t) (i : w64) (vs : list ?V) (dq : dfrac)
         (v : ?V) (Φ : val → iPropI Σ),
         s ↦*{dq} vs ∗ ⌜vs !! uint.nat i = Some v⌝ -∗
         ▷ (s ↦*{dq} vs -∗ Φ (# v)) -∗
         WP ![# ?t] (# (slice.elem_ref_f s ?t i)) {{ v, Φ v }}
where
?V :
  [Σ : gFunctors
   hG : heapGS Σ
   goGlobalsGS0 : goGlobalsGS Σ
   H : heap.GlobalAddrs
  |- Type]
?IntoVal0 :
  [Σ : gFunctors
   hG : heapGS Σ
   goGlobalsGS0 : goGlobalsGS Σ
   H : heap.GlobalAddrs
  |- IntoVal ?V]
?t :
  [Σ : gFunctors
   hG : heapGS Σ
   goGlobalsGS0 : goGlobalsGS Σ
   H : heap.GlobalAddrs
  |- go_type]
?IntoValTyped0 :
  [Σ : gFunctors
   hG : heapGS Σ
   goGlobalsGS0 : goGlobalsGS Σ
   H : heap.GlobalAddrs
  |- IntoValTyped ?V ?t]
```

::::

We got this specification using `Check` rather than copying it from the Perennial source code. Notice that the Hoare triple notation is not used here (I'm not entirely sure why, possibly a bug in the notations). You should still be able to read this specification, if you understood the "continuation-passing style" encoding of Hoare triple used in Iris.

The one complication with this particular specification is that its precondition requires the caller to pass the value `v0` that is in the slice. `SliceGet` itself requires `i` to be in-bounds (otherwise `s[i]` panics in Go), and `vs !! uint.nat i = Some v0` has the side of enforcing this obligation, and the postcondition then uses the same value `v0`.

Storing into a slice requires a proof `is_Some (vs !! uint.nat i)`, which similarly guarantees that `i` is in-bounds, but the original value is not needed. The postcondition uses `<[uint.nat i := v]> vs` which is a Gallina implementation of updating one index of a list (it's notation for the function `insert` from std++).

You may notice that there's an arbitrary `q : dfrac` in the specification for `SliceGet`, while `SliceSet` has `DfracOwn 1`. This difference is no accident and corresponds to the fact that `SliceGet` works even on a _read-only_ slice while `SliceSet` needs to be able to modify the input slice. We'll cover the mechanism with fractions [later on](#read-only).

### Appending to a slice

The capacity of a slice is interesting in the model because it turns out ownership of the capacity is separate from ownership of the elements. Consider the following code, which splits a slice:

```go
s := []int{1,2,3}
s1 := s[:1]
s2 := s[1:]
```

What is not obvious in this example is that `s1` has a capacity that _overlaps_ with that of `s2`. Specifically, the behavior of this code is surprising (you can [run it yourself](https://go.dev/play/p/yhcjYdVBVjo) on the Go playground):

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

- `own_slice_small s dq t xs` asserts ownership only over the elements within the length of `s`, and says they have values `xs`.
- `own_slice_cap s t` asserts ownership over just the capacity of `s`, saying nothing about their contents (but they must have type `t`).
- `own_slice s dq t xs := own_slice_small s dq t xs ∗ own_slice_cap s t` asserts ownership over the elements and capacity.

These predicates are just definitions that are separating conjunctions over regular points-to facts for the elements. In the context of the example above, with `s = (ptr, 3, 4)` (notice we picked a capacity of 4), these predicates are equal to the following:

- `own_slice_small s [1;2;3] = (ptr + 0) ↦ 1 ∗ (ptr + 1) ↦ 2 ∗ (ptr + 2) ↦ 3`
- `own_slice_cap s [1;2;3] = ∃ x, (ptr + 3) ↦ x`
- ```
  own_slice_small (s[1:]) [2; 3]
   = ((ptr + 1) + 0) ↦ 2 ∗ ((ptr + 1) + 1) ↦ 3
   = (ptr + 1) ↦ 2 ∗ (ptr + 2) ↦ 3
  ```

Confirm for yourself that `own_slice_small` and `own_slice_cap` are disjoint; without that, `own_slice` wouldn't be useful since it would be equivalent to $\False$.

The main specification related to capacity is the one for append:

```coq
Lemma wp_SliceAppend s t vs x :
  {{{ own_slice s t (DfracOwn 1) vs ∗ ⌜val_ty x t⌝ }}}
    SliceAppend t s x
  {{{ s', RET slice_val s'; own_slice s' t (DfracOwn 1) (vs ++ [x]) }}}.
```

Notice that `own_slice` appears in the pre- and post-condition; it would be unsound to use `own_slice_small` here, since appending modifies the capacity of a slice.

What is key to understanding the Go example above is that the Go expression `s[:n]` is ambiguous as to how it handles ownership. The capacity of `s[:n]` and `s[n:]` overlap; if we model `s[:n]` with `slice_take s n` and `s[n:]` as `slice_drop s n`, then there are two main choices for how to divide ownership when taking a prefix:

- `own_slice s dq t xs ⊢ own_slice (slice_take s dq t (take xs n))`. Drop any ownership over the elements after `n`, but retain the capacity of the smaller slice.
- `own_slice_small s dq t xs ⊢ own_slice_small (slice_take s dq t (take xs n)) ∗ own_slice_small (slice_drop s dq t (drop xs n))`. Split ownership, but lose the ability to append to the prefix.

There is one more possibility which is a slight variation on splitting:

- `own_slice s dq t xs ⊢ own_slice_small (slice_take s dq t (take xs n)) ∗ own_slice (slice_drop s dq t (drop xs n))`. If we start out with ownership of the capacity, we can split ownership and still be able to append to the _second_ part (its capacity is the capacity of the original slice). We can actually derive this from the lower-level fact that `slice_cap s t ⊣⊢ slice_cap (slice_skip s n)` if `n` is in-bounds.

### Exercise: find the theorems above in Perennial

Either using `Search` or by looking at the source code in Perennial, find the theorems above.

The relevant source code is the file `src/goose_lang/lib/slice/typed_slice.v` in Perennial (you can use the submodule copy in your exercises repo).

### Exercise: attempt a proof outline for the append example

Try to use the predicates and rules for slice ownership to give a proof outline for the append example. At some point you will get stuck, because the reasoning principles don't give a way to verify the code above - this is fine in that we don't really intend to verify odd code like the above, but seeing exactly where you get stuck is instructive for learning how the rules work.

## Read-only ownership: fractional permissions {#read-only}

Fractional permissions are an approach to reasoning about read-only access in separation logic.

This concept is explained as part of the Program Proofs guide in [fractional permissions](./program-proofs/fractions.md).

```coq
End goose.
```
