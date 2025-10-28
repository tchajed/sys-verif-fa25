---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture-note
tags: literate
shortTitle: "Abstraction"
order: 4
date: 2025-09-14 8:00:00 -5
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Model-based specifications for functional programs

> Follow these notes in Rocq at [src/sys_verif/notes/adt_specs.v](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/src/sys_verif/notes/adt_specs.v).

## Learning outcomes

From reading this note, you should be able to

1. State the correctness of a functional Abstract Data Type (ADT) using a model
2. Articulate what guarantees various model-based specifications provide
3. Compare equational specifications to model-based specifications

In this note, we'll start getting into how to write specifications, beginning with functional programs.

Remember the core idea of verification: every verification task combines code + spec + proof. This must be sound (the proof should convince you, and a computer, that the spec holds for the code). The code ought to be useful. But what about the spec? There isn't "one true spec" for each program - it depends on what you want to do with it.

For functional programs, there are a few different styles you might use. In this lecture we'll focus on a style of specification well suited to verifying (or just informally reasoning about) _clients_ of the functional program.

The basic idea is that when you have something called an Abstract Data Type (ADT) - some data type and associated functions to use it - you can prove that it behaves like an _abstract model_. The specification we show is enough to enable a client to reason about their own code without referencing your code, only the model.

## Example 1: big numbers

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

```rocq
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

## Example 2: map with deletions

The abstraction in this example is a simple map, but the implementation is more complex: it tracks both a normal map of elements and a set of deleted keys. Such an implementation might be useful if the map is large and it is desirable to make deletions fast (at the cost of slower lookups). A more sophisticated implementation would also normalize the data structure, occasionally removing an element from both the `elements` map and `deletions` set, in order to avoid unbounded growth of the deletions set.

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
    destruct (elements m !! k') as [v0|] eqn:Hgetk'.
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

### Invariant-based ADT specification

The strategy we saw in the previous note is good, but we can make it better. There are cases where you have code and a model, and the code always behaves like the model, but the above strategy doesn't work.

The issue is that we might need an _invariant_ for the code to be correct. The specifications above ask the developer to prove the abstraction is correct for every operation and getter function for any input of type `T`; however, some values of type `T` may never be produced by this library. Typically with an ADT we can rely on the client to only use the provided methods (that's what the "abstract" in "abstract data type" means), so our code should only have to be correct for data it can actually produce.

The way to address this is to change the specification we prove to incorporate an invariant, so that all the proofs (a) show the invariant is preserved at all times, and (b) we relate the code to the model only when the invariant holds. We'll see how the client reasoning above still works, so that the specification still shows that any client can substitute the model and think about the model rather than the code.

An ADT consists of:

- A type `T` (the _code_ or _concrete_ representation) of the data type.
- Initialization (constructors or "introduction"). For some `A: Type`, `init: A → T`
- Methods: for some `A: Type`, `op: T → A → T`
- Getters ("eliminators"): of the form `f: T → A` for some `A: Type`.

Exactly as before, we first need a model of the ADT we want to prove it against:

1. Create a model with `S: Type`, `init_spec : A → S`, `op_spec : S → A → S`, and `f_spec : S → A`.

The difference is how we connect the ADT code to the model:

2. Pick an abstraction function `rep : T → S` and also pick an invariant `inv : T → Prop`.
3. Prove the following obligations for each function:
   - For `init_spec : A → S`, prove `∀ (v: A), rep (init v) = init_spec v` AND `∀ v, inv (init v)`.
   - For `op_spec : S → A → S`, prove `∀ (x: T) (v: A), inv x → rep (op x v) = op_spec (rep x) v ∧ inv (op x v)`.
   - For `f_spec: S → A`, prove `∀ (x: T), inv x → f x = f_spec (rep x)`.

First, observe how these obligations prove that any value `y: T` produced from using this interface will satisfy `inv y` - this is what it means for it to be an "invariant".

Second, notice that we get to assume `inv x` as a premise, which is what makes this more powerful, but we're also on the hook to prove `inv x` is actually initially true and maintained (to justify assuming it). Invariants are tricky to come up with for this reason. However, without the ability to use an invariant, these obligations require reasoning about any value of type `T`, which may just be impossible

Finally, a small observation: the specification style is _strictly_ more powerful than without invariants; we can always pick `inv x = True` and then it's the same as if we didn't have an invariant at all, but there are examples an ADT and an associated model that we can prove are related only with invariants.

### Exercise: re-do client-centric reasoning with invariants

- $T : \mathrm{Type}$
- $i : T$
- $op_1 : T \to T$ and $op_2 : T \to T$
- $f : T \to A$

And the spec:

- $S : \mathrm{Type}$, $rep : T \to S$, and $inv : T \to \mathrm{Prop}$
- $i' : S$
- $op_1' : S \to S$ and $op_2' : S \to S$
- $f' : S \to A$

Prove that $f' (op_2' (op_1'(i'))) = f (op_2 (op_1 (i)))$ using the theorems above. (Note we typically write $f(x)$ for blackboard/on-paper reasoning on the blackboard/paper while the same function application is written `f x` in Rocq).

:::: important What is the "specification"?

Sometimes the word "specification" refers just to the abstract model of some code; we will be precise. Other times, it refers to the whole theorem that relates the code to the abstract model. You should try to keep these concept distinct in your mind even if you see the word used for either meaning. We will use "abstraction" to precisely refer to the abstract model, and reserve "specification" for a theorem, which might relate the code to an abstraction using one of the styles of specification described here (for functional programs).

We've seen only one type of abstract model, but two specification styles for relating the code to the abstract model - the one with invariants is strictly more general, so that's the one you should keep in mind. Later, we'll start doing verification where the code will no longer be a functional program and will need to revisit the connection and state a new specification theorem.

::::

## Proven example: binary search tree

```rocq
Inductive search_tree :=
| leaf
| node (el: Z) (l r: search_tree).

```

This example's proofs illustrate use of the `gset` type from std++. In the future we won't go over its implementation at all (it's fairly complicated), but will use it to write specifications. Sets are nice in that we get the quite powerful `set_solver` automation; it's not quite as magical as `lia` but still fairly powerful.

On a first pass you can read this example ignoring the proofs - just read the code, abstraction function, invariant, and spec _theorem statements_.

```rocq
Fixpoint st_rep (t: search_tree) : gset Z :=
  match t with
  | leaf => ∅
  | node el l r => {[el]} ∪ st_rep l ∪ st_rep r
  end.

```

The binary search tree invariant references the abstraction function, which happens to be the easiest way in this case to find all the elements in the left and right subtrees.

```rocq
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

```rocq
Lemma empty_spec :
  st_rep st_empty = ∅ ∧ st_inv st_empty.
Proof.
  split.
  - reflexivity.
  - simpl.
    auto.
Qed.

```

Look at the specifications below to see how we incorporate the invariant.

It has two goals, one about the new abstract state, and the other showing the invariant is preserved: in both cases we can assume `st_inv t` from the previous operation, specifically because (1) the invariant starts out true for every constructor, and (2) every operation comes with a proof that the invariant is preserved.

```rocq
Lemma insert_spec t x :
  st_inv t →
  st_rep (st_insert t x) = st_rep t ∪ {[x]} ∧
  st_inv (st_insert t x).
Proof.
  induction t.
  - intros Hinv.
    simpl.
    set_solver.
  - intros Hinv.
    simpl in Hinv.
    split.
    + simpl.
      destruct (decide (x < el)).
      * simpl.
         set_solver.
      * destruct (decide (el < x)).
         { set_solver. }
         assert (x = el) by lia.
         set_solver.
    + simpl.
      destruct (decide (x < el)); simpl.
      * set_solver.
      * destruct (decide (el < x)); simpl.
        { set_solver. }
        assert (x = el) by lia.
        intuition.
Qed.

```

The invariant is crucially needed to prove that `find` is correct - a binary search tree doesn't work if the nodes have arbitrary values, because then it wouldn't always search the correct path. The work we've done above has mainly been so we can assume `st_inv` here.

```rocq
Lemma find_spec t x :
  st_inv t →
  st_find t x = bool_decide (x ∈ st_rep t).
Proof.
  (* this follows directly from the definition of [bool_decide] *)
  replace (bool_decide (x ∈ st_rep t)) with
    (if decide (x ∈ st_rep t) then true else false)
    by reflexivity.
  induction t.
  - simpl. intros Hinv.
    set_solver.
  - simpl. intros Hinv.
    destruct (decide (x < el)).
    + destruct Hinv as (Hlt & Hgt & Hinvt1 & Hinvt2).
      rewrite IHt1.
      { auto. }
      destruct (decide (x ∈ st_rep t1)).
      * rewrite decide_True //. set_solver.
      * rewrite decide_False //.
```

:::: info Goal

```txt
  el : Z
  t1, t2 : search_tree
  x : Z
  n : x ∉ st_rep t1
  IHt1 : st_inv t1 → st_find t1 x = false
  IHt2 :
    st_inv t2
    → st_find t2 x = (if decide (x ∈ st_rep t2) then true else false)
  Hlt : ∀ x : Z, x ∈ st_rep t1 → x < el
  Hgt : ∀ y : Z, y ∈ st_rep t2 → el < y
  Hinvt1 : st_inv t1
  Hinvt2 : st_inv t2
  l : x < el
  ============================
  x ∉ {[el]} ∪ st_rep t1 ∪ st_rep t2
```

::::

```rocq
        (* We will prove that x is not in each of these three parts. We already
        have [x ∉ st_rep t1] by assumption. *)
        assert (x ≠ el) by lia.
        (* x being on the right side is a contradiction: we are in a branch
        (from much earlier) where [x < el] but on the right side of the tree [el
        < y]. *)
        assert (x ∉ st_rep t2).
        { intros Hel.
          apply Hgt in Hel.
          lia. }
        set_solver.
    + (* This branch is when [x ≥ el]. *)
      destruct Hinv as (Hlt & Hgt & Hinvt1 & Hinvt2).
      destruct (decide (el < x)).
      * rewrite -> IHt2 by auto.
        (* NOTE: you could do the rest of this proof with more basic techniques,
        as above. This is a more automated version. *)
        clear IHt1. (* needed to make [destruct] pick the right instance *)
        destruct (decide _); destruct (decide _); set_solver by lia.
      * assert (x = el) by lia.
        rewrite decide_True //.
        set_solver.
Qed.

```

## Invariant vs non-invariant spec styles

A specification has two sides: the perspective of the implementor proving it, in which case it's an _obligation_, and the perspective of the client using it, in which case it's an _assumption_. In general the implementor wants (a) true obligations (they can't prove something false) and (b) simple obligations (if possible, they want to prove something easier than something harder). The client wants (a) strong enough to reason about their own code, and (b) easy-to-use specifications are preferred to strong but hard-to-understand ones.

There is a tension here that the abstract spec is trying to balance.

When we add invariants to the model-based specification, the benefit is that it allows us to prove _more ADTs correct_, and in fact many ADTs are only correct because they maintain some internal invariant (the implementor now has a hope of proving their code against this specification, like in the search tree example). There's no cost to the client, either, since essentially the same client reasoning works regardless of what the invariant is.

## Extension 2: abstraction relations {#abstraction-relations}

There's one more extension beyond invariants that allows us to verify even more examples. Instead of an abstraction function `abs : T → S`, we can instead have an **abstraction relation** `abs_rel : T → S → Prop`, which you can think of as answering for each `T`, what are the possible values of `S` that could be the current abstract state? There might not be _any_ values of `S`, which corresponds to a `T` that doesn't satisfy the invariant, or there might be one unique one like we had before with the abstraction function.

One reason you would want this is that the most obvious specification or model has more information than the code actually tracks. For an example, consider a "statistics database" that tracks the running sum and number of elements as elements are added and is able to report the mean of the elements added so far (this example is implemented and verified below). In the model, we would track all the elements. But then there's no function from the code state to the spec: the code intentionally forgets information, but it can still answer what the mean is at any time. This example is nonetheless provable with an abstraction relation.

Another direction you might want to think about how we could add non-determinism to both the code operations and the spec operations, although this will take us away from functional programs so we won't consider it just yet.

```rocq
Module stat_db.
  Unset Printing Records.


```

We use `Record` here to create an inductive type, which defines a constructor `mkDb` as well as _projection functions_ `db_sum` and `db_num`.

Records in Rocq have some special associated syntax for constructors and projections, but we're not using it (and disable printing with that syntax as well).

```rocq
  Record database :=
    mkDb { db_sum : Z; db_num : Z; }.

  Definition empty_db : database := mkDb 0 0.
  Definition insert_el (x: Z) (db: database) :=
    mkDb (db_sum db + x) (db_num db + 1).
  (* We're going to ignore division by zero. Coq makes [x / 0 = 0] which is how
  this function will also work (this makes good mathematical sense which I'm
  happy to explain, but it doesn't affect this example). *)
  Definition mean (db: database) : Z :=
    db_sum db / db_num db.

  Definition failed_rep_function (db: database) : list Z := []. (* where do we get this from? *)

  Definition listZ_sum (s: list Z) :=
    foldl (λ s x, s + x) 0 s.

  Definition absr (db: database) (s: list Z) :=
    db_sum db = listZ_sum s ∧
    db_num db = Z.of_nat (length s).

  Lemma insert_el_spec x db s :
    absr db s →
    absr (insert_el x db) (s ++ [x]).
  Proof.
    rewrite /absr /=.
    destruct db as [sum num]; simpl.
    intros [Heq1 Heq2]. rewrite Heq1. rewrite Heq2.
    split.
    - rewrite /listZ_sum.
      rewrite foldl_app /=.
      reflexivity.
    - rewrite length_app /=.
      lia.
  Qed.

  (* this theorem follows pretty much immediately from the definitions of [absr]
  and [mean]; the work is in maintaining [absr], not in this theorem *)
  Lemma mean_spec db s :
    absr db s →
    mean db = listZ_sum s / (Z.of_nat (length s)).
  Proof.
    rewrite /absr /=.
    destruct db as [sum num]; simpl.
    (* instead of using [rewrite] we use [subst] because if `x = ...` and `x` is
    a variable, we can replace it everywhere and then the equation is
    redundant. *)
    intros [? ?]; subst.
    rewrite /mean /=.
    reflexivity.
  Qed.

End stat_db.

```

### Alternative specification: equational specifications

A completely different style than the above is to give _equational_ or _algebraic_ specifications. An example where this makes a lot of sense is `encode`/`decode` functions. The main property we generally want of such functions (as a _client_ or user of such code) is a "round trip" theorem that says `∀ x, decode (encode x) = x`. An equational specification is exactly what we want here, and there isn't even an obvious "model" to describe encoding or decoding if we tried to use a model-based specification.

The danger of equational or algebraic specifications is that it's harder to think about whether the specification is good enough for client reasoning - in general we need to give specs for any combination of functions. However, it has the advantage of not requiring an abstraction.

### Equational spec for maps

Here is an ADT implementing maps that we'll prove equational properties for, rather than relating it to `gmap`. Think of this as what you would do if _implementing_ `gmap`, except we'll discuss later how `gmap` has a more complicated implementation to make it easier to use.

```rocq
Definition list_map (K: Type) {H: EqDecision K} (V: Type) :=
  list (K * V).

```

Sections are a way of writing a bunch of definitions that need to take the same types, like the `K`, `H: EqDecision K`, and `V` parameters for `list_map`.

```rocq
Section list_map.

(* To understand the code below, all you need to know is that `K` and `V` are
defined as arbitrary types by this `Context` command. When the section is
closed, all of these will become arguments to the definitions in the section for
any users of this code (and there are no users yet for this little example). *)
Context {K: Type} {H: EqDecision K} {V: Type}.

Definition empty_list_map : list_map K V := [].

Fixpoint find (x: K) (m: list_map K V) : option V :=
  match m with
  | [] => None
  | (x', v) :: m' => if decide (x = x') then Some v else find x m'
  end.

Definition update (x : K) (v: V) (m: list_map K V) : list_map K V :=
  (x, v) :: m.

```

What equations might we want? One idea is that we should prove something about any combinations of `find` and `update` we can think of (that type check).

```rocq
Lemma find_empty_list_map x :
  find x empty_list_map = None.
Proof. reflexivity. Qed.

Lemma find_update_eq (m: list_map K V) x v :
  find x (update x v m) = Some v.
Proof.
  rewrite /update. simpl.
  rewrite -> decide_True by auto.
  reflexivity.
Qed.

Lemma find_update_neq (m: list_map K V) x y o :
  x ≠ y → find x (update y o m) = find x m.
Proof.
  intros Hne.
  rewrite /update. simpl.
  rewrite -> decide_False by auto.
  reflexivity.
Qed.

End list_map.
```
