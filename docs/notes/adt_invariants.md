---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture-note
tags: literate
shortTitle: "ADTs with invariants"
order: 5
pageInfo: ["Date", "Category", "Tag", "Word"]
---

## ADT specification with invariants

> Follow these notes in Rocq at [src/sys_verif/notes/adt_invariants.v](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/src/sys_verif/notes/adt_invariants.v).

### Learning outcomes

1. State a model-based specification for an ADT with an invariant
2. Compare equational specifications to model-based specifications

### Invariant-based ADT specification

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

Prove that $f' (op_2' (op_1'(i'))) = f (op_2 (op_1 (i)))$ using the theorems above. (Note we typically write $f(x)$ for blackboard/on-paper reasoning on the blackboard/paper while the same function application is written `f x` in Coq).

:::: important What is the "specification"?

Sometimes the word "specification" refers just to the abstract model of some code. Other times, it refers to the whole theorem that relates the code to the abstract model. You should try to keep these concept distinct in your mind even if you see the word used for either meaning.

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
    + destruct Hinv as (Hlt & Hgt & Hinvt1 & Hinvt2).
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

### Alternative specification: equational specifications

A completely different style than the above is to give _equational_ or _algebraic_ specifications. An example where this makes a lot of sense is `encode`/`decode` functions. The main property we generally want of such functions (as a _client_ or user of such code) is a "round trip" theorem that says `∀ x, decode (encode x) = x`. There isn't even an obvious "model" to describe encoding or decoding.

The danger of equational or algebraic specifications is that it's harder to think about whether the specification is good enough for client reasoning - in general need to give specs for any combination of functions. It has the advantage of not requiring an abstraction.

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

```

At this point, have we proven all the equations that might be needed? I believe so, but it's hard to be sure, and the situation is worse when we have many operations that can interact with each other.

```rocq
End list_map.

```

## Extension 2: abstraction relations {#abstraction-relations}

There's one more extension beyond invariants that allows us to verify even more examples. Instead of an abstraction function `abs : T → S`, we can instead have an **abstraction relation** `abs_rel : T → S → Prop`, which you can think of as answering for each `T`, what are the possible values of `S` that could be the current abstract state? There might not be _any_ values of `S`, which corresponds to a `T` that doesn't satisfy the invariant, or there might be one unique one like we had before with the abstraction function.

One reason you would want this is that the most obvious specification or model has more information than the code actually tracks. For an example, consider a "statistics database" that tracks the running sum and number of elements as elements are added and is able to report the mean of the elements added so far (this example is implemented and verified below). In the model, we would track all the elements. But then there's no function from the code state to the spec: the code intentionally forgets information, but it can still answer what the mean is at any time. This example is nonetheless provable with an abstraction relation.

Another direction you might want to think about how we could add non-determinism to both the code operations and the spec operations, although this will take us away from functional programs so we won't consider it just yet.

```rocq
Module stat_db.
  Unset Printing Records.


```

We use `Record` here to create an inductive type, which defines a constructor `mkDb` as well as _projection functions_ `db_sum` and `db_num`.

Records in Coq have some special associated syntax for constructors and projections, but we're not using it (and disable printing with that syntax as well).

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
