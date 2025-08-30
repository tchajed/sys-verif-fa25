---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture
tags: literate
shortTitle: "Lecture 4: ADT specification"
order: 4
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Lecture 4: Model-based specifications for functional programs

> Follow these notes in Rocq at [src/sys_verif/notes/adt_specs.v](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/src/sys_verif/notes/adt_specs.v).

## Learning outcomes

By the end of this lecture, you should be able to

1. State the correctness of a functional Abstract Data Type (ADT) using a model
2. Understand how to use `gmap`

In this lecture, we'll start getting into how to write specifications, beginning with functional programs.

Remember the core idea of verification: every verification task combines code + spec + proof. This must be sound (the proof should convince you, and a computer, that the spec holds for the code). The code ought to be useful. But what about the spec? There isn't "one true spec" for each program - it depends on what you want to do with it.

For functional programs, there are a few different styles you might use. In this lecture we'll focus on a style of specification well suited to verifying (or just informally reasoning about) _clients_ of the functional program.

The basic idea is that when you have something called an Abstract Data Type (ADT) - some data type and associated functions to use it - you can prove that it behaves like an _abstract model_. The specification we show is enough to enable a client to reason about their own code without referencing your code, only the model.

## Illustrative example: big numbers

Suppose we want to represent numbers of arbitrary size. One way to do this is with a list of digits, using the built-in `list` type.

```rocq
Definition digit := Z.
Definition big_int := list digit.

```

Now we need some operations to do things with `big_int`s.

```rocq
Definition zero : big_int := [].
(* This is only intended to work when `0 ≤ x < 10`. *)
Definition from_digit (x: digit) : big_int := [x].

```

The next operation that will be part of the "public interface" is `big_int_add`, but defining that operation requires some helper functions.

```rocq
Definition digit_sum_carry (d1 d2: digit): (digit * digit) :=
  ((d1 + d2) `mod` 10, (d1 + d2) `div` 10).

(* a quick test case *)
#[local]
Lemma __digit_sum_carry_test :
  (* 7 + 5 = 12 *)
  digit_sum_carry 7 5 = (2, 1).
Proof. reflexivity. Qed.

Fixpoint add_one (b : big_int) (d : digit) : big_int :=
  match b with
  | [] => if decide (d = 0) then [] else [d]
  | h :: t =>
      let (sum, carry) := digit_sum_carry h d in
      sum :: add_one t carry
  end.

Fixpoint add_with_carry (b1 b2 : big_int) (carry : digit) : big_int :=
  match b1, b2 with
  | [], [] => if decide (carry = 0) then [] else [carry]
  | d1 :: t1, [] => add_one (d1 :: t1) carry
  | [], d2 :: t2 => add_one (d2 :: t2) carry
  | d1 :: t1, d2 :: t2 =>
      let (sum, new_carry) := digit_sum_carry d1 d2 in
      add_one (sum :: add_with_carry t1 t2 new_carry) carry
  end.

Definition big_int_add (b1 b2 : big_int) : big_int :=
  add_with_carry b1 b2 0.

```

Finally, we'll provide a comparison function for big integers:

```rocq
Definition big_int_le (b1 b2: big_int) : bool.
Admitted. (* exercise for the reader *)

```

To summarize, the interface to the code we export to the client (which we'll have to write a spec for) consists of the following signatures:

```coq
Definition big_int : Type.

Definition zero : big_int.
(** requires [0 ≤ x < 10] *)
Definition from_digit (x: Z) : big_int.

Definition big_int_add: big_int -> big_int -> big_int.
Definition big_int_le : big_int -> big_int -> bool.
```

The user of this implementation should not need to know the definitions of any of these.

The core idea of a _model-based specification_ is to relate this code to a spec based on a model of `big_int`. In this case, the natural model is that a `big_int` represents an integer. We can view all of the operations as manipulating this abstract integer (even if it never appears in the code), and that's exactly what the spec will show.

The specification needs to pick a consistent way to relate a `big_int` to the abstract `Z` it represents, which we call an _abstraction function_. The function uses the suffix `_rep` for "representation" since it gives what a `i: big_int` represents in the abstract model.

```rocq
Definition rep_type := Z.
Fixpoint big_int_rep (i: big_int) : rep_type :=
  match i with
  | [] => 0
  | d :: i => d + 10 * big_int_rep i
  end.

```

After picking an abstraction function, we relate all of the code to specifications using `Z` and its related functions. The pattern might be easiest to pick out from the example, but we'll shortly present it generically as well.

```rocq
Lemma zero_spec : big_int_rep zero = 0.
Proof. reflexivity. Qed.

Lemma from_digit_spec x :
  0 ≤ x < 10 →
  big_int_rep (from_digit x) = x.
Proof.
  intros. simpl.
```

:::: info Goal

```txt
  x : Z
  H : 0 ≤ x < 10
  ============================
  x + 10 * 0 = x
```

::::

```rocq
 lia.
Qed.

(* I've written this using `Z.add` rather than infix `+` just to make the
pattern more obvious. *)
Lemma big_int_add_spec : forall i1 i2,
  big_int_rep (big_int_add i1 i2) = Z.add (big_int_rep i1) (big_int_rep i2).
Proof.
Admitted.

Lemma big_int_le_spec : forall i1 i2,
  big_int_le i1 i2 = bool_decide (big_int_rep i1 ≤ big_int_rep i2).
Proof.
Admitted.

```

## Exercise: model of relational database

What do you think is the model of a relational database? To make this concrete, consider a database with two tables, "Artists" and "Albums", that have the following schemas:

- Artists: ArtistId as INTEGER, Name as TEXT
- Albums: AlbumId as INTEGER, Title as TEXT, ArtistId as Integer

What type would be the model of a database in this schema? That is, if we were writing `db_rep : database -> M` what should `M` be?

### Example 2: map with deletions

```rocq
(* This Module just groups the definitions so we can use short names inside. *)
Module deleteMap.

(* the values in the map don't matter so we pick something arbitrary *)
Notation V := nat.

(* This type of inductive is common enough that we could replace this
boilerplate with the [Record] feature. We use an inductive only to avoid
introducing new syntax. *)
Inductive map :=
  | mkMap (elements: gmap Z V) (deletions: gset Z).
Definition elements (m: map) : gmap Z V :=
  match m with
  | mkMap elements _ => elements
  end.
Definition deletions (m: map) : gset Z :=
  match m with
  | mkMap _ deletions => deletions
  end.

(* The underscore will distinguish these names from the std++ map definitions,
which we'll use as the spec. *)
Definition empty_ : map := mkMap ∅ ∅.
Definition insert_ (k: Z) (v: V) (m: map) : map :=
  mkMap (insert k v (elements m)) (deletions m ∖ {[k]}).
Definition remove_ (k: Z) (m: map) : map :=
  mkMap (elements m) (deletions m ∪ {[k]}).
Definition lookup_ (k: Z) (m: map) : option V :=
  if decide (k ∈ deletions m) then None
  else (elements m) !! k.

Definition rep (m: map) : gmap Z V :=
  (* to remove all the deletions, we filter to the (k, v) pairs where k is _not_
  deleted *)
  filter (λ '(k, v), k ∉ deletions m) (elements m).

Lemma empty_spec : rep empty_ = ∅.
Proof.
  rewrite /rep /=.
  reflexivity.
Qed.
Lemma insert_spec k v m : rep (insert_ k v m) = insert k v (rep m).
Proof.
  rewrite /rep /=.
  apply map_eq. intros k'.
  destruct (decide (k' = k)).
  - subst. rewrite lookup_insert_eq.
    apply map_lookup_filter_Some.
    rewrite lookup_insert_eq.
    split.
    + auto.
    + set_solver.
  - rewrite lookup_insert_ne //.
    (* figured this out by trial and error (after finding the two relevant
    lemmas) *)
    rewrite map_filter_insert_True.
    { set_solver. }
    rewrite lookup_insert_ne //.
    (* The proof from here is complicated. We have to break it down into cases
    where the map_lookup_fiter_* lemmas apply; some additional lemmas about the
    interaction of lookup and filter would help, but we don't need them to do
    the proof (and we could state and prove those lemmas). *)
    destruct (decide (k' ∈ deletions m)).
    {
      rewrite map_lookup_filter_None_2.
      { set_solver. }
      rewrite map_lookup_filter_None_2.
      { set_solver. }
      auto.
    }
    destruct (elements m !! k') as [v0|] eqn:Heqk'.
    + transitivity (Some v0).
      { apply map_lookup_filter_Some. split; auto. set_solver. }
      symmetry.
      apply map_lookup_filter_Some. set_solver.
    + rewrite -> map_lookup_filter_None_2 by set_solver.
      rewrite -> map_lookup_filter_None_2 by set_solver.
      auto.
Qed.

Lemma remove_spec k m : rep (remove_ k m) = delete k (rep m).
Proof.
  rewrite /rep /=.
  apply map_eq. intros k'.
  destruct (decide (k' = k)).
  - subst. rewrite lookup_delete_eq.
    apply map_lookup_filter_None.
    set_solver.
  - rewrite lookup_delete_ne //.
    admit.
Admitted.

Lemma lookup_spec k m : lookup_ k m = (rep m) !! k.
Proof.
  rewrite /rep /=.
  rewrite /lookup_.
  destruct (decide _).
  - rewrite map_lookup_filter_None_2 //.
    set_solver.
  - destruct (elements m !! k) eqn:H.
    + symmetry.
      apply map_lookup_filter_Some_2; auto.
    + rewrite map_lookup_filter_None_2 //.
      set_solver.
Qed.
End deleteMap.

```

## Model-based specification

This is the generic form of the spec we saw above for big integers.

Starting point: want to verify an Abstract Data Type (ADT, not to be confused with _algebraic data type_). An ADT consists of:

- A type `T` (the _code_ or _concrete_ representation) of the data type.
- Initialization (constructors or "introduction"). For some `A: Type`, `init: A → T`
- Methods: for some `A: Type`, `op: T → A → T`
- Getters ("eliminators"): of the form `f: T → A` for some `A: Type`.

A specification for an ADT is constructed similarly:

1. Come up with a model for the code.
   - Pick a type `S` that will be the _abstract_ representation (or _model_) of the data of type `T`. (Note: in general, `S` will not efficient in the programming language, or might not even be representable).
   - Write a version of each code function in terms of the abstract type `S` rather than `T`: `init_spec : A → S`, `op_spec : S → A → S`, and `f_spec : S → A`.
2. To relate the code to the model, invent an _abstraction function_ `rep : T → S` giving what abstract value the code is representing.
3. Prove the following obligations that relate the code to the model via the abstraction function:
   - For `init_spec : A → S`, prove `∀ (v: A), rep (init v) = init_spec v`.
   - For `op_spec : S → A → S`, prove `∀ (x: T) (v: A), rep (op x v) = op_spec (rep x) v`.
   - For `f_spec: S → A`, prove `∀ (x: T), f x = f_spec (rep x)`.

::: important Model-based specifications

Make sure you can follow what the specifications above are actually saying. It might not all make sense at this point but after seeing examples come back to this description. We'll revisit it a couple more times as the basis for specifying imperative and concurrent programs, where the code will be more sophisticated and we'll need to do more work to relate the code to the model, which will remain mathematical functions.

:::

Why prove the above? These obligations show that any sequence of operations can be understood in terms of model (the `_spec` variants of each function), even though we run the concrete versions. For example this code:

```
let x := init c1;
let y := do_op1 x;
let z := do_op2 y;
let r := get_result z;
r
```

This whole process produces `get_result (do_op2 (do_op1 (init c1)))` when the code is run. We can instead view this as the following sequence, using the model:

```
let x' := init_spec c1;
let y' := do_op1_spec x';
let z' := do_op1_spec y';
let r' := get_result_spec z';
r'
```

**Claim:** `r' = r` if the data structure satisfies the specs described above.

We can use the proofs above to prove this claim that `r' = r`, using simple equational reasoning; at each step we are applying one obligation from the above.

```
  r
= get_result      (do_op2      (do_op1      (init c1)))
= get_result_spec (abs (do_op2 (do_op1      (init c1))))
= get_result_spec (do_op2_spec (abs (do_op1 (init c1))))
= get_result_spec (do_op2_spec (do_op1_spec (abs (init c1))))
= get_result_spec (do_op2_spec (do_op1_spec (init_spec c1)))
= r'
```

:::: important Client-centric reasoning

The fact that proving a model-based specification _implies_ the sort of client reasoning above is a crucial point. Remembering the form of the specification is nice, but it's even more important to see this justification for why prove this spec at all. Later we'll extend the strategy but we will always want to maintain the ability for a client to reason about their code with the model.

::::

Sometimes described as a **commutative diagram** (though this term has a very specific meaning in category theory which is likely the more common usage of "commutative diagram").

Notice that the client reasoning does not depend on `rep`; it is a detail of the proof that explains _why_ the code is correct, but is not necessary to understand _what the code does_. On the other hand if you were verifying the code you would certainly care about what `rep` is since it directly shows up in all of the proof obligations, and if you were implementing this library you also might want to have a model in mind and think about how each code state maps to it.

Also notice that the model - `S` and all the spec variants - were invented as part of the spec, but aren't inheret to the code. You can even imagine proving the same code relates to two different models.

## Extension 1: code invariants

The above strategy is good, but we can make it better. There are cases where you have code and a model, and the code always behaves like the model, but the above strategy doesn't work.

The issue is that we might need an _invariant_ for the code to be correct. The specifications above ask the developer to prove the abstraction is correct for every operation and getter function for any input of type `T`; however, some values of type `T` may never be produced by this library. Typically with an ADT we can rely on the client to only use the provided methods (that's what the "abstract" in "abstract data type" means), so our code should only have to be correct for data it can actually produce.

The way to address this is to change the specification we prove to incorporate an invariant, so that all the proofs (a) show the invariant is preserved at all times, and (b) we relate the code to the model only when the invariant holds. We'll see how the client reasoning above still works, so that the specification still shows that any client can substitute the model and think about the model rather than the code.

## Exercise: derive model-based specifications with invariants

Make an attempt to write the proof obligations for a model-based specification that incorporates an invariant over the data, adapting the strategy above. Think about what would make your strategy _sound_ in justifying the reasoning above that converted the code functions to spec functions.

In the next lecture we'll start with this specification.
