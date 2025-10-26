---
# Auto-generated from literate source. DO NOT EDIT.
tags: literate
shortTitle: Decidable equality
---

# Decidable equality

What is this `if decide` thing? And what is `bool_decide`? And how do I do proofs involving them?

The basic answer is that if you want to write functional code with an `if` over a proposition (often an equality `a = b`), you must wrap the proposition in `decide`. The reason is that in general, Rocq's theory doesn't permit testing arbitrary propositions, but for specific ones it is possible to provide an algorithm for testing them, showing that they are "decidable" (in the same sense as in complexity theory). For example, we can provide such a decidability algorithm for equality over most plain data types.

The way we _access_ these decidability implementations is using `decide`, which is implemented using Rocq Typeclasses.

```rocq
From stdpp Require Import numbers.
From sys_verif Require Import options.
From Coq.Arith Require Import Peano_dec.

```

We often use the pattern `if decide P then ... else ...`. Alternately, you may try to write `if (x = y) then ... else ...` it will fail, in which case you _should_ be writing `if decide (x = y) then ... else ...`. Alternately, you may see `bool_decide` or `decide` show up in program proofs since they are used by Goose.

This explanation gives you a terse overview of how `decide` works and how to do proofs involving it.

If your goal involves `decide`, one thing you can do is `destruct (decide P)`, which will split into two cases:

```rocq
(* this theorem is obviously false, it's just a demo of the proof tactics *)
Lemma example_destruct_1 (x y: Z) :
  (if decide (x = y) then (x+1) else (y-2)) = 7.
Proof.
  destruct (decide (x = y)).
```

:::: info Goals

```txt title="goal 1"
  x, y : Z
  e : x = y
  ============================
  x + 1 = 7
```

```txt title="goal 2"
  x, y : Z
  n : x ≠ y
  ============================
  y - 2 = 7
```

::::

Notice the `x ≠ y` hypothesis in the second goal. This is how `~(x = y)` is printed. You will see `~(x < y)` if you destruct an inequality; `lia` and `word` know how to deal with that.

```rocq
Abort.

Lemma example_destruct_2 (x y: Z) :
  (if decide (x = y) then (x+1) else (y-2)) = 7.
Proof.
  (* You can pass a pattern with underscores to `destruct` and it will fill them
  in with anything seen in the goal; this isn't specific to `decide` but the two
  are often convenient together. This has the same effect as `destruct (decide (x = y))` in this goal. *)
  destruct (decide _).
Abort.

Lemma example_destruct_3 (x y: Z) :
  (if decide (x = y) then (x+1) else (y-2)) = 7.
Proof.
  (* You can pass a pattern with underscores to `destruct` and it will fill them
  in with anything seen in the goal; this isn't specific to `decide` but the two
  are often convenient together. This has the same effect as `destruct (decide (x = y))` in this goal. *)
  destruct (decide _).
Abort.

```

## bool_decide

In some contexts you will see `bool_decide` and not `decide`. It also takes a proposition as an argument, but produces a boolean, which is sometimes needed in program proofs or other contexts. There are a few lemmas and tricks to work with it.

Here's a cheatsheet:

- The tactic `case_bool_decide` to destruct a `bool_decide` and do a proof in each case.
- `rewrite bool_decide_eq_true_2` gives `bool_decide P = true` and produces `P` as a side condition
- `rewrite bool_decide_eq_false_2` gives `bool_decide P = false` and produces `~P` as a side condition

First of all, you don't want to do `destruct (bool_decide P)` like we did above.

```rocq
Lemma bad_bool_decide_destruct (x y: Z) :
  3 ≤ (if bool_decide (x < 3) then 3 else x).
Proof.
  destruct (bool_decide _).
```

:::: info Goals

```txt title="goal 1"
  x, y : Z
  ============================
  3 ≤ 3
```

```txt title="goal 2"
  x, y : Z
  ============================
  3 ≤ x
```

::::

```rocq
  - lia.
  - (* not provable: we have nothing about `~(x < 3)` *)
Abort.

Lemma example_bool_decide_destruct (x y: Z) :
  3 ≤ (if bool_decide (x < 3) then 3 else x).
Proof.
  case_bool_decide.
```

:::: info Goals

```txt title="goal 1"
  x, y : Z
  H : x < 3
  ============================
  3 ≤ 3
```

```txt title="goal 2"
  x, y : Z
  H : ¬ x < 3
  ============================
  3 ≤ x
```

::::

```rocq
  - lia.
  - (* this is provable *)
    lia.
Qed.

Lemma example_bool_decide_rewrite (x y: Z) :
  x < 1 →
  (if bool_decide (x < 3) then x else y) = x.
Proof.
  intros Hlt.
  (* I'd usually do `rewrite bool_decide_eq_true_2 //` to automatically prove
  the trivial subgoals (the second one in this case), but want to illustrate the goals here. *)
  rewrite bool_decide_eq_true_2.
```

:::: info Goals

```txt title="goal 1"
  x, y : Z
  Hlt : x < 1
  ============================
  x < 3
```

```txt title="goal 2"
  x, y : Z
  Hlt : x < 1
  ============================
  x = x
```

::::

```rocq
  - lia.
  - rewrite //.
Qed.

```

## Missing Decision P instance

The second thing you may encounter is that sometimes, `decide P` won't type check because of a missing `Decision P` instance:

```rocq
Inductive color := red | green | blue.
Fail Definition failed_color_dec (c: color) :=
  if decide (c = red) then true else false.
```

:::: note Output

```txt

```

::::

You should really read the error message and try to make sense of it.

The reason this fails is that `Decision P` says that there's a _function_ that determines if P is true vs if ~P is true. Coq's logic is such that we actually can't do this for arbitrary propositions `P`; it requires that we can _compute_ which of `P` or `~P` is true.

`decide` is just looking up this function using typeclasses, but the actual function doesn't get implemented for us automatically. We can provide an instance of equality between arbitrary colors; here's a manual version of that which we'll abandon in favor of using the powerful `solve_decision` automation tactic.

```rocq
Instance color_eq_dec : ∀ (c1 c2: color), Decision (c1 = c2).
Proof.
  intros c1 c2. rewrite /Decision.
  destruct c1, c2.
```

:::: info Goals

```txt title="goal 1"
  ============================
  {red = red} + {red ≠ red}
```

```txt title="goal 2"
  ============================
  {red = green} + {red ≠ green}
```

```txt title="goal 3"
  ============================
  {red = blue} + {red ≠ blue}
```

```txt title="goal 4"
  ============================
  {green = red} + {green ≠ red}
```

```txt title="goal 5"
  ============================
  {green = green} + {green ≠ green}
```

::::

```rocq
  - left. auto.
  - right. congruence.
  (* Yikes, this looks tedious. *)
Abort.

Instance color_eq_dec : ∀ (c1 c2: color), Decision (c1 = c2).
Proof. solve_decision. Qed.

```

Now Coq will use the instance we just defined when we write `decide`.

```rocq
Definition use_color_dec (c: color) := if decide (c = red) then true else false.

```

## Implementation

The implementation (which comes from std++) is actually very short, so let's show that.

If you're unfamiliar with typeclasses, you might want to start by reading this [tutorial on typeclasses](https://softwarefoundations.cis.upenn.edu/qc-current/Typeclasses.html).

```rocq
Module decide_playground.
  (* `decide` is the single member of a type class `Decision P` *)
  Class Decision (P : Prop) := decide : {P} + {~P}.


```

What is that type for `decide`? `{P} + {~P}` is notation for `sumbool` from the Coq standard library, which has the following definition:

```rocq
  Inductive sumbool (A B : Prop): Type :=
  | left (H: A)
  | right (H: B).


```

This definition says `sumbool A B` has either an element of `A` or a proof of `B`, and I call them proofs because `A` and `B` are `Prop`s. This is the Curry-Howard correspondence: we call a proposition `P` true if it has an `pf:   P`, and we call such an element a proof. See Software Foundations's [Curry-Howard Correspondence chapter](https://softwarefoundations.cis.upenn.edu/lf-current/ProofObjects.html) for more.

The definition of `sumbool` is actually the same as `or P Q` (always written `P ∨ Q`), except that it is annotated as `{P} + {Q} : Type` whereas `P   ∨ Q : Prop`. The difference is that we can do computations with something in `Type`, while facts in `Prop` can only be used in proofs.

```rocq
End decide_playground.
```
