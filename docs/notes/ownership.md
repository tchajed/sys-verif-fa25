---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture
tags: literate
order: 13
shortTitle: "Lecture 13: Ownership in Go"
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Lecture 13: Goose - Ownership reasoning

> Follow these notes in Coq at [src/sys_verif/program_proof/ownership.v](https://github.com/tchajed/sys-verif-fa24-proofs/blob/main/src/sys_verif/program_proof/ownership.v).

## Learning outcomes

1. Understand the assertions for structs in Goose.
2. State the right ownership over a slice for a function.
3. Use and understand fractional permissions in specifications.

Theme for today: ownership in Go and in GooseLang

---

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
From Goose.sys_verif_code Require heap.

Section goose.
Context `{hG: !heapGS Σ}.

```

Goose does actually model struct values as tuples, and doesn't (yet) have a better way to write them in specs.

In practical use, we typically define a Gallina record and relate these records to the GooseLang representation, and then most specs work with the Gallina record and not with these tuples.

Notice also that there's an extra unit value at the end; this makes the recursive functions for accessing fields much simpler.

```coq
Lemma wp_ExamplePerson :
  {{{ True }}}
    heap.ExamplePerson #()
  {{{ RET (#"Ada", (#"Lovelace", (#25, #()))); True }}}.
Proof.
  wp_start as "_".
  wp_pures.
  iModIntro.
  iApply "HΦ".
  done.
Qed.

Lemma String_app_empty_l s :
  "" +:+ s = s.
Proof.
  unfold String.app.
  reflexivity.
Qed.

(* shockingly, this is not in the standard library *)
Lemma String_app_assoc (s1 s2 s3: string) :
  (s1 +:+ s2) +:+ s3 = s1 +:+ s2 +:+ s3.
Proof.
  induction s1; simpl.
  - rewrite !String_app_empty_l //.
  - rewrite !String_append.
    congruence.
Qed.

Lemma wp_Person__Name (firstName lastName: string) (age: w64) :
  {{{ True }}}
    heap.Person__Name (#firstName, (#lastName, (#age, #())))
  {{{ RET #(str (firstName ++ " " ++ lastName)); True }}}.
Proof.
  wp_start as "_".
  wp_pures.
  wp_rec. wp_pures.
  iModIntro.
  iDestruct ("HΦ" with "[]") as "HΦ".
  { done. }
  iExactEq "HΦ".
  f_equal.
  f_equal.
  f_equal.
  rewrite String_app_assoc //.
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

The postcondition of the following spec introduces the _struct field points-to_. `l ↦[heap.Person :: "Age"] #(W64 25)` combines calculating an offset from `l` for the Age field of Person (that is, computing `l +ₗ #2`) with asserting that the value at that location is `#25`.

```coq
Lemma wp_ExamplePersonRef :
  {{{ True }}}
    heap.ExamplePersonRef #()
  {{{ (l: loc), RET #l;
      l ↦[heap.Person :: "FirstName"] #(str "Ada") ∗
      l ↦[heap.Person :: "LastName"] #(str "Lovelace") ∗
      l ↦[heap.Person :: "Age"] #(W64 25)
  }}}.
Proof.
  wp_start as "_".
  wp_apply wp_allocStruct.
  { val_ty. }
  iIntros (p) "Hperson".
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  Φ : val → iPropI Σ
  p : loc
  ============================
  "HΦ" : ∀ l : loc,
           l ↦[heap.Person::"FirstName"] #(str "Ada") ∗
           l ↦[heap.Person::"LastName"] #(str "Lovelace") ∗
           l ↦[heap.Person::"Age"] #(W64 25) -∗ Φ #l
  "Hperson" : p ↦[struct.t heap.Person] (#(str "Ada"),
                                         (#(str "Lovelace"), (#(W64 25), #())))
  --------------------------------------∗
  Φ #p
```

::::

Notice in the goal above how the struct allocation produced a `p ↦[struct.t heap.Person] v` assertion. This is actually the same as the points-to assertion we've been using all along, albeit with a more complex type. This assertion actually says that `v` is a tuple with the right structure to be a `Person` struct, and its three values are laid out in memory starting at `p`.

Now look at what the following line of proof does to the goal.

```coq
iApply struct_fields_split in "Hperson"; iNamed "Hperson".
```

:::: info Goal diff

```txt title="goal diff"
  Σ : gFunctors
  hG : heapGS Σ
  Φ : val → iPropI Σ
  p : loc
  ============================
  "HΦ" : ∀ l : loc,
           l ↦[heap.Person::"FirstName"] #(str "Ada") ∗
           l ↦[heap.Person::"LastName"] #(str "Lovelace") ∗
           l ↦[heap.Person::"Age"] #(W64 25) -∗ Φ #l
  "Hperson" : p ↦[struct.t heap.Person] (#(str "Ada"), // [!code --]
                                         (#(str "Lovelace"), (#(W64 25), #()))) // [!code --]
  "FirstName" : p ↦[heap.Person::"FirstName"] #(str "Ada") // [!code ++]
  "LastName" : p ↦[heap.Person::"LastName"] #(str "Lovelace") // [!code ++]
  "Age" : p ↦[heap.Person::"Age"] #(W64 25) // [!code ++]
  --------------------------------------∗
  Φ #p
```

::::

The theorem `struct_fields_split` gives a way to take any points-to assertion with a struct type and split it into its component field points-to assertions, which is what the postcondition of this spec gives.

```coq
iApply "HΦ".
  iFrame.
Qed.

Lemma wp_Older (firstName lastName: string) (age: w64) (p: loc) (delta: w64) :
  {{{ p ↦[heap.Person :: "FirstName"] #firstName ∗
      p ↦[heap.Person :: "LastName"] #lastName ∗
      p ↦[heap.Person :: "Age"] #age
  }}}
    heap.Person__Older #p #delta
  {{{ RET #();
      p ↦[heap.Person :: "FirstName"] #firstName ∗
      p ↦[heap.Person :: "LastName"] #lastName ∗
      (* we avoid overflow reasoning by saying the resulting integer is just
      [word.add age delta], which will wrap at 2^64  *)
      p ↦[heap.Person :: "Age"] #(LitInt (word.add age delta))
  }}}.
Proof.
  wp_start as "H".
  iDestruct "H" as "(first & last & age)".
  wp_pures.
  (* there's a tactic to struct field loads/stores as well *)
  wp_loadField.
  wp_storeField.
  iModIntro.
  iApply "HΦ".
  iFrame.
Qed.

```

Here is one spec for `GetAge`, which results in breaking off the age field into its points-to assertion.

```coq
Lemma wp_GetAge (firstName lastName: string) (age: w64) (p: loc) (delta: w64) :
  {{{ "first" :: p ↦[heap.Person :: "FirstName"] #firstName ∗
      "last" :: p ↦[heap.Person :: "LastName"] #lastName ∗
      "age" :: p ↦[heap.Person :: "Age"] #age
  }}}
    heap.Person__GetAge #p
  {{{ (age_l: loc), RET #age_l;
      p ↦[heap.Person :: "FirstName"] #firstName ∗
      p ↦[heap.Person :: "LastName"] #lastName ∗
      age_l ↦[uint64T] #age
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_apply wp_struct_fieldRef.
  { simpl. auto. }
  iApply "HΦ".
  iFrame.
  iExactEq "age".
  rewrite struct_field_pointsto_eq.
  reflexivity.
Qed.

```

## Slices

Go has a slice type `[]T`, a generic type that works for any element type `T`. Slices in Go are implemented as a struct value with a pointer, a length, and a capacity; this is also how they are modeled in GooseLang.

### What are slices?

You can read more about them in this post on [Go data structures](https://research.swtch.com/godata) or in even more detail in this [post on slices and append](https://go.dev/blog/slices). Below are some basic details.

A slice represents a piece of a contiguous block of memory, which is often called an array.

The length of a slice is the number of elements of valid data the slice references starting at the pointer. The capacity tracks how many additional elements past the length are available for the slice to grow to, if elements are appended.

In Go, the common idiom for appending to a slice `s []T` is `s = append(s, x)`. This is because if `s` has no spare capacity, `append` allocates a new, larger array and copies the elements over to it; this cannot change `s` since this is passed by value, so instead the new slice is returned. When a slice is grown, typically its capacity will be double the original length, to amortize the cost of copying over the elements.

### Reasoning about slices

The basic assertion for working with slices is `own_slice s t dq xs`. `s` is a `Slice.t`, a Coq record representing the slice value (the triple of pointer, length, and capacity); in GooseLang code, you will instead use `slice_val s : val`. `t` is the type of elements, similar to the types used for structs and struct fields. `dq` is a fraction, explained below; for now we will pretend like it's always `DfracOwn 1`. Finally, `xs` is a Gallina `list` of the elements of the slice. The overall result is an assertion that gives ownership over the slice `s`, and records that it has the elements `xs`.

This abstraction uses typeclasses so the type of `xs` can vary, so for example we can use `list w64` for a slice of integers. You can see this in the type signature for `own_slice`, where there are parameters `V: Type` and `IntoVal V`:

```coq
About own_slice.
```

:::: note Output

```txt title="coq output"
own_slice :
∀ {ext : ffi_syntax} {ffi : ffi_model} {ffi_interp0 : ffi_interp ffi}
  {Σ : gFunctors},
  heapGS Σ
  → ∀ {ext_ty : ext_types ext} {V : Type},
      IntoVal V → Slice.t → ty → dfrac → list V → iProp Σ

own_slice is not universe polymorphic
Arguments own_slice {ext ffi ffi_interp0 Σ heapGS0 ext_ty}
  {V}%type_scope {IntoVal0} s t%heap_type q vs%list_scope
own_slice is transparent
Expands to: Constant Perennial.goose_lang.lib.slice.typed_slice.own_slice
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

```coq
Check wp_SliceGet.
```

:::: note Output

```txt title="coq output"
wp_SliceGet
     : ∀ (stk : stuckness) (E : coPset) (s : Slice.t)
         (t : ty) (q : dfrac) (vs : list ?V) (i : w64)
         (v0 : ?V) (Φ : val → iPropI Σ),
         own_slice_small s t q vs ∗ ⌜vs !! uint.nat i = Some v0⌝ -∗
         ▷ (own_slice_small s t q vs -∗ Φ (to_val v0)) -∗
         WP SliceGet t s #i @ stk; E {{ v, Φ v }}
where
?V : [Σ : gFunctors  hG : heapGS Σ |- Type]
?IntoVal0 : [Σ : gFunctors  hG : heapGS Σ |- IntoVal ?V]
```

::::

We got this specification using `Check` rather than copying it from the Perennial source code. Notice that the Hoare triple notation is not used here (I'm not entirely sure why, possibly a bug in the notations). You should still be able to read this specification, if you understood the "continuation-passing style" encoding of Hoare triple used in Iris.

The one complication with this particular specification is that its precondition requires the caller to pass the value `v0` that is in the slice. `SliceGet` itself requires `i` to be in-bounds (otherwise `s[i]` panics in Go), and `vs !! uint.nat i = Some v0` has the side of enforcing this obligation, and the postcondition then uses the same value `v0`.

```coq
Check wp_SliceSet.
```

:::: note Output

```txt title="coq output"
wp_SliceSet
     : ∀ (stk : stuckness) (E : coPset) (s : Slice.t) (t : ty),
         IntoValForType ?V t
         → ∀ (vs : list ?V) (i : w64) (v : ?V) (Φ : val → iPropI Σ),
             own_slice_small s t (DfracOwn 1) vs ∗
             ⌜is_Some (vs !! uint.nat i)⌝ -∗
             ▷ (own_slice_small s t (DfracOwn 1) (<[uint.nat i:=v]> vs) -∗
                Φ #()) -∗ WP SliceSet t s #i (to_val v) @ stk; E {{ v, Φ v }}
where
?V : [Σ : gFunctors  hG : heapGS Σ |- Type]
?IntoVal0 : [Σ : gFunctors  hG : heapGS Σ |- IntoVal ?V]
```

::::

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

Goose accurately models this situation. It does so by separating out the predicates for ownership of a slice's elements (between 0 and its length) and its capacity (from length to capacity).

- `own_slice_small s dq t xs` asserts ownership only over the elements within the length of `s`, and says they have values `xs`.
- `own_slice_cap s t` asserts ownership over just the capacity of `s`, saying nothing about their contents (but they must have type `t`).
- `own_slice s dq t xs := own_slice_small s dq t xs ∗ own_slice_cap s t` asserts ownership over the elements and capacity.

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

## Read-only ownership: fractional permissions {#read-only}

Fractional permissions are an approach to reasoning about read-only access in separation logic.

This concept is explained as part of the Program Proofs guide in [fractional permissions](./program-proofs/fractions.md).

```coq
End goose.
```
