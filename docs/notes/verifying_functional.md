---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture
tags: literate
shortTitle: "Lecture 4: Functional specifications"
order: 4
---

# Lecture 4: Model-based specifications for functional programs

## Learning outcomes

By the end of this lecture, you should be able to

1. State the correctness of a functional program using an abstract model

In this lecture, we'll start getting into how to write specifications, beginning with functional programs.

Remember the core idea of verification: every verification task combines code + spec + proof. This must be sound (the proof should convince you, and a computer, that the spec holds for the code). The code ought to be useful. But what about the spec? There isn't "one true spec" for each program - it depends on what you want to do with it.

For functional programs, there are a few different styles you might use. In this lecture we'll focus on a style of specification well suited to verifying (or just informally reasoning about) _clients_ of the functional program. The perspective here is that you have a set of functions, but you don't want to read the code at all (because it's too complicated). Instead, we'll write specs for the code that are enough to use it and to show that your client code produces the right answers.

The basic idea is to come up with an _abstract model_ of your data.

## Illustrative example: big numbers

Suppose we want to represent numbers of arbitrary size. One way to do this is with a list of digits, using the built-in `list` type.

```coq
Definition digit := Z.
Definition big_int := list digit.

```

Now we need some operations to do things with `big_int`s.

```coq
Definition zero : big_int := [].
(* This is only intended to work when `0 ≤ x < 10`. *)
Definition from_digit (x: digit) : big_int := [x].

```

The next operation that will be part of the "public interface" is `big_int_add`, but defining that operation requires some helper functions.

```coq
Definition digit_sum_carry (d1 d2: digit): (digit * digit) :=
  (d1 + d2 `mod` 10, d1 + d2 `div` 10).

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

```coq
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

```coq
Definition rep_type := Z.
Fixpoint big_int_rep (i: big_int) : rep_type :=
  match i with
  | [] => 0
  | d :: i => d + 10 * big_int_rep i
  end.

```

After picking an abstraction function, we relate all of the code to specifications using `Z` and its related functions. The pattern might be easiest to pick out from the example, but we'll shortly present it generically as well.

```coq
Lemma zero_spec : big_int_rep zero = 0.
Proof. reflexivity. Qed.

Lemma from_digit_spec x :
  0 ≤ x < 10 →
  big_int_rep (from_digit x) = x.
Proof.
  intros. simpl.
```

:::: info Goal

```txt title="goal 1"
  x : Z
  H : 0 ≤ x < 10
  ============================
  x + 10 * 0 = x
```

::::

```coq
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

:::: details Solution

One answer, from database theory, is the relational model of a database.

In that model, a database is a collection of _relations_ (what we often call "tables"), where a relation is a set of _tuples_ (what we often think of as a "rows"). Note that the original formulation really had a _set_, so that the there were no duplicate rows and the rows were unordered. Practically speaking they must be ordered in some way in a computer, and for efficiency reasons duplicates are often allowed. Furthermore the tuples were intended to be a mapping from field names to values that were also unordered, but we won't try to capture that exactly here.

Thus one answer is that we use the following:

```coq
Record Artist := {
  ArtistId: Integer;
  Name: Text;
}.

Record Album := {
  AlbumId: Integer;
  Title: Text;
  ArtistId: Integer;
}.

Record database_model := {
  Artist_relation: gset Artist;
  Album_relation: gset Album;
}.
```

Databases also often have integrity constraints. It wasn't stated above, but it's natural that any valid database would have a unique `ArtistId` for every element of the `Artist_relation` and unique `AlbumId` (because these are _primary keys_). There's also an implied _foreign key_ relationship where every `ArtistId` appearing in the albums relation is in the artists relation.

These ought to be captured by proving that every abstract `database_model` that comes up from the implementation has the above consistency properties. These are distinct from invariants of the code, even though they have many similarities.

::::

## Model-based specification

This is the generic form of the spec we saw above for big integers.

Starting point: have some data structure or other object of type T (the _code_ or _concrete_ representation). It consists of:

- Initialization (constructors or "introduction"). For some `A: Type`, `init: A → T`
- Methods: for some `A: Type`, `op: T → A → T`
- Getters ("eliminators"): of the form `f: T → A` for some `A: Type`.

1. The first step is to pick a type `S` that will be the _abstract_ representation (or _model_) of the data of type `T`. (Note: in general, `S` will not efficient in the programming language, or might not even be representable).
2. Invent an _abstraction function_ `rep : T → S` giving what abstract value the code is representing.
3. Prove specs for each function:
   - Write `init_spec : A → S`. Prove `∀ (v: A), rep (init v) = init_spec v`.
   - Write `op_spec : S → A → S`. Prove `∀ (x: T) (v: A), rep (op x v) = op_spec (rep x) v`.
   - Write `f_spec: S → A`. Prove `∀ (x: T), f x = f_spec (rep x)`.

::: important Model-based specifications

Make sure you can follow what the specifications above are actually saying. It might not all make sense at this point but after seeing examples come back to this description. We'll revisit it a couple more times as the basis for specifying imperative and concurrent programs.

:::

Why prove the above? These obligations show that any sequence of operations can be understood in terms of `_spec` variants, even though we run the concrete versions:

```
let x := init c1;
let y := do_op1 x;
let z := do_op2 y;
let r := get_result z;
r
```

This whole process produces `get_result (do_op2 (do_op1 (init c1)))` when the code is run. But at an abstract level we could just as well have written:

```
let x' := init_spec c1;
let y' := do_op1_spec x';
let z' := do_op1_spec y';
let r' := get_result_spec z';
r'
```

**Claim:** `r' = r` if the data structure satisfies the specs described above. (Check that you believe this!)

:::: important Client-centric reasoning

The fact that proving a model-based specification _implies_ the sort of client reasoning above is a crucial point. Remembering the form of the specification is nice, but it's even more important to see this justification for why prove this spec at all. Later we'll extend the strategy but we will always want to maintain the ability for a client to reason about their code with the model.

::::

Sometimes described as a **commutative diagram** (though this term has a very specific meaning in category theory which is likely the more common usage of "commutative diagram").

Notice that the claim does not depend on `rep`; it is a detail of the proof that explains _why_ the code is correct, but is not necessary to understand _what the code does_. On the other hand if you were verifying the code you would certainly care about what `rep` is, and if you were writing it you also might want to think about how each code state maps to the desired abstraction.

Also notice that `S` and all the spec variants were invented as part of the spec. You can even imagine two different specs for the same code.

## Extension 1: code invariants

The above strategy is _sound_ in that it gets the desired client reasoning. However, it is _incomplete_: there are correct data structures where the above process doesn't work (it requires proving impossible specifications).

**Stop and think for a minute**: is this good? What would a complete but unsound method look like?

:::: details Solution

**An unsound proof strategy is no proof strategy at all**! From the perspective of someone looking at such a claimed proof, it gives no new information at all. If it's complete this doesn't help; as soon as it's unsound it might as well just say everything is true.

Incompleteness is certainly an issue, but it is a common theoretical limitation for powerful theorems. We have to go beyond this fact and think about whether the technique is powerful enough for practical examples, and what we would do if it fails (eg, switch to a different strategy, or change the code, or change the specification).

::::

One example where the specification technique as stated doesn't work is actually the big num example from the beginning of this chapter: it turns out the theorems above aren't true as stated! The issue is that there are examples of values `i : big_int` that are invalid, but the theorem expects proofs `∀ (i: big_int)`.

The code isn't incorrect, though, because it actually maintains an _invariant_ over `big_int`s: all digits always satisfy `0 ≤ d < 10` (they initially do and then this invariant remains true, hence why we call it "invariant").

## Exercise: derive model-based specifications with invariants

Make an attempt to write the proof obligations for a model-based specification that incorporates an invariant over the data, adapting the strategy above. Think about what would make your strategy _sound_ in justifying the reasoning above that converted the code functions to spec functions.

:::: details Model-based specifications, with a code invariant

1. Same as above, pick `S`.
2. Pick `rep` but also pick `inv : T → Prop`.
3. Prove specs for each function:
   - Write `init_spec : A → S`. Prove `∀ (v: A), rep (init v) = init_spec v` (as above) AND `∀ v, inv (init v)`.
   - Write `op_spec : S → A → S`. Prove `∀ (x: T) (v: A), inv x → rep (op x v) = op_spec (rep x) v ∧ inv (op x v)`.
   - Write `f_spec: S → A`. Prove `∀ (x: T), inv x → f x = f_spec (rep x)`.

Notice the strategy is _strictly_ more powerful; we can always pick `inv x = True` and then it's the same as above.

Second, notice that we get to assume `inv x` as a premise, which is what makes this more powerful, but we're also on the hook to prove `inv x` is actually initially true and maintained (to justify assuming it). Invariants are tricky for this reason.

::::

## Proven example: binary search tree

```coq
Inductive search_tree :=
| leaf
| node (el: Z) (l r: search_tree).

```

This example illustrates use of the `gset` type from std++. We won't go over its implementation at all (it's fairly complicated), but will use it to write specifications.

```coq
Fixpoint st_rep (t: search_tree) : gset Z :=
  match t with
  | leaf => ∅
  | node el l r => {[el]} ∪ st_rep l ∪ st_rep r
  end.

Fixpoint st_inv (t: search_tree) : Prop :=
  match t with
  | leaf => True
  | node el l r =>
      (∀ x, x ∈ st_rep l → x < el) ∧
      (∀ y, y ∈ st_rep r → el < y) ∧
      st_inv l ∧
      st_inv r
  end.

Definition st_empty : search_tree := leaf.

Fixpoint st_insert (t: search_tree) (x: Z) : search_tree :=
match t with
  | leaf => node x leaf leaf
  | node el l r =>
      if decide (x < el) then
        node el (st_insert l x) r
      else if decide (el < x) then
        node el l (st_insert r x)
      else
        t  (* x is already in the tree, so no changes *)
  end.

Fixpoint st_find (t: search_tree) (x: Z) : bool :=
  match t with
  | leaf => false  (* x is not found in an empty tree *)
  | node el l r =>
      if decide (x < el) then
        st_find l x
      else if decide (el < x) then
        st_find r x
      else
        true  (* x is found *)
  end.

```

With an invariant, it's important to prove it holds at initialization time.

```coq
Lemma empty_spec :
  st_rep st_empty = ∅ ∧ st_inv st_empty.
Proof.
  split.
  - reflexivity.
  - simpl.
    auto.
Qed.

```

Notice how we incorporate the invariant into this proof of an operation.

You can think of it as two goals, one about the new abstract state, and the other showing the invariant is preserved: in both cases we can assume `st_inv t` from the previous operation, specifically because (1) the invariant starts out true for every constructor, and (2) every operation comes with a proof that the invariant is preserved.

```coq
Lemma insert_spec t x :
  st_inv t →
  st_rep (st_insert t x) = st_rep t ∪ {[x]} ∧
  st_inv (st_insert t x).
Proof.
  induction t.
  - simpl.
    set_solver.
  - simpl.
    destruct (decide (x < el)).
    + simpl. set_solver.
    + destruct (decide (el < x)).
      * simpl. set_solver.
      * simpl.
        assert (x = el) by lia.
        set_solver.
Qed.

Lemma find_spec t x :
  st_inv t →
  st_find t x = bool_decide (x ∈ st_rep t).
Proof.
  replace (bool_decide (x ∈ st_rep t)) with
    (if decide (x ∈ st_rep t) then true else false)
    by reflexivity.
  intros Hinv.
  induction t.
  - simpl.
    set_solver.
  - simpl.
    destruct (decide (x < el)).
    + simpl.
      simpl in Hinv. destruct Hinv as (Hlt & Hgt & Hinvt1 & Hinvt2).
      rewrite IHt1.
      { auto. }
      destruct (decide (x ∈ st_rep t1)).
      * rewrite decide_True //. set_solver.
      * rewrite decide_False //.
        (* We will prove that x is not in each of these three parts. We already have `x ∉ st_rep` by assumption. *)
        assert (x ≠ el) by lia.
        (* x being on the right side is a contradiction: we are in a branch
        (from much earlier) where [x < el] but on the right side of the tree [el
        < y]. *)
        assert (x ∉ st_rep t2).
        { intros Hel.
          apply Hgt in Hel.
          lia. }
        set_solver.
    + simpl in Hinv. destruct Hinv as (Hlt & Hgt & Hinvt1 & Hinvt2).
      destruct (decide (el < x)).
      * rewrite -> IHt2 by auto.
        (* NOTE: you could do the rest of this proof with the more basic
        techniques, as above. This is a more automated version. *)
        clear IHt1. (* needed to make [destruct] pick the right instance *)
        destruct (decide _); destruct (decide _); set_solver by lia.
      * assert (x = el) by lia.
        rewrite decide_True //.
        set_solver.
Qed.

```

## Beyond the above specification

### Non-determinism: abstraction relations

There's one more extension that is natural to add at some point: non-determinism. Instead of `abs : T → S` (a function), we can instead have `abs_rel : T → S → Prop`, which you can think of as answering for each `T`, what are the possible values of `S` that could be the current abstract state? There might not be _any_ values of `S`, which corresponds to a `T` that doesn't satisfy the invariant, or there might be one unique one like we had before with the abstraction function.

One reason this comes up is that the most obvious specification or model has more information than the code actually tracks. For example, consider a "statistics database" that tracks the running sum and number of elements as elements are added and is able to report the mean of the elements added so far. In the model, we would track all the elements. But then there's no function from the code state to the spec: the code intentionally forgets information, but it can still answer what the mean is at any time. This example is nonetheless provable with an abstraction relation.

Another direction you might want to think about how we could add non-determinism to both the code operations and the spec operations, although this will take us away from functional programs so we won't consider it just yet.

### Equational specifications

A completely different style than the above is to give _equational_ or _algebraic_ specifications. An example where this makes a lot of sense is `encode`/`decode` functions. The main property we generally want of such functions (as a _client_ or user of such code) is a "round trip" theorem that says `∀ x, decode (encode x) = x`. There isn't even an obvious "model" to describe encoding or decoding.

The danger of equational or algebraic specifications is that it's harder (and not systematic) to think about whether the specification is good enough for client reasoning. However, in the encode/decode example it's at some level it's necessary for the clients purposes to prove the round-trip property mentioned above.
