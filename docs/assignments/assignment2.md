---
order: 3
shortTitle: "Assignment 2"
icon: pen-fancy
---

# Assignment 2: Separation Logic theory

::: info

This is a theory assignment: you'll submit written responses rather than doing proofs in a computer.

:::

In this assignment, you'll answer some questions about Hoare logic and separation logic on paper rather than submitting mechanized proofs. The goal is to build and exercise your mental model for the specifications, proof rules, and program proofs, without having to work out all the details or translate your argument to something Coq understands. The two downsides are that you have to do all the calculations yourself, and there's no computer patiently checking your work and confirming when you're done; you'll have to think about it and wait for (much slower) feedback from me.

$$
\gdef\hoare#1#2#3{\left\{#1\right\} \, #2 \, \left\{#3\right\}}
\gdef\True{\mathrm{True}}
\gdef\False{\mathrm{False}}
\gdef\rec#1#2{\text{\textbf{rec} } #1 \; #2.\;\,}
\gdef\fun#1{\lambda #1.\,}

\gdef\sep{\mathbin{\raisebox{1pt}{$\star$}}}
\gdef\pointsto{\mapsto}
\gdef\emp{\mathrm{emp}}
$$

**Exercise 1:** [Prove the rule of consequence](../notes/hoare.md#ex-soundness-consequence) for Hoare logic, from the soundness definition for a Hoare triple.

**Exercise 2:** For each separation logic proposition below, describe precisely the set of heaps where it is true. Briefly explain if you think it's warranted (or if you're unsure of your answer). Assume a linear separation logic.

Note that the overlapping conjunction $(P \land Q)(h)$ is defined to be true when $P(h)$ and $Q(h)$. While not commonly used, this is a perfectly valid separation logic proposition.

- (a) $\exists v.\, \ell \pointsto v$
- (b) $\exists \ell'.\, \ell' \pointsto v$
- (c) $\forall v.\, \ell \pointsto v$
- (d) $(\ell \pointsto v) \sep (\True \land \emp)$
- (e) $\ell \pointsto v \land \ell \pointsto v$
- (f) $\ell \pointsto v \sep \ell \pointsto v$
- (g) $(\exists v.\, \ell_1 \pointsto v) \sep (\exists \ell.\, \ell \pointsto \num{3})$
- (h) $(\exists v.\, \ell \pointsto v) \land (\exists \ell'.\, \ell' \pointsto \num{3})$
- (i) $(\exists x. \lift{x > 2}) \sep (\exists x. \lift{x < 2})$

**Exercise 3:** Compare the separation logic frame rule to the rule for weakening. Explain why the weaken rule does not imply the frame rule. Explain why the frame rule does not imply the weaken rule.

**Exercise 4:** Your friend Ben Bitdiddle has read the section on [recursion and loops](../notes/sep-logic.md#recursion-loops) and thinks he has found a bug in separation logic. He claims to have proven the following triple:

$$\hoare{\True}{(\rec{f}{x} f \, x) \, ()}{\fun{\_} \False}$$

"This proves False with no hypotheses, which makes separation logic unsound!" he exclaims, a little too excited at having broken what you spent so much time learning.

What do you say to Ben?

**Exercise 5:** We will develop a linked list implementation and give it a specification using a _representation predicate_. This is the separation logic analog to the ADT specifications we saw earlier for functional programs. The model of a linked list will be a Coq `list`, as expected; its code will be an implementation in our "lecture notes" programming language, which I'll call `expr`.

This problem will follow the presentation of linked lists in [Robbert Krebbers's program verification course](https://gitlab.science.ru.nl/program-verification/course-2023-2024/-/blob/master/lectures/week10.md). Be careful reading the notation: code in the language is written in Coq syntax, with type annotations to clarify what's going on, but these are not functional programs. The types are mostly straightforward to understand, except that `ref T` is used for a pointer to a `T` (ref stands for "reference"); a value of this type will always be a location, and when dereferenced will return a value of type `T`. The syntax `alloc`, `!x`, and `x ← v` is the same as our programming language.

Our language did not have a way of doing pattern matching, which makes it awkward to implement linked lists. For the purpose of this exercise let's assume it has a way to represent this inductive type for a linked list holding values of type `A`:

```coq title="expr"
llist A :=
| lnil 
| lcons (hd: A) (tl: ref (llist A))
```

Notice that this is not like the Coq `list A` type in that the `tl` field is a _pointer_ to the rest of the list.

To use this inductive, we need pattern matching. Assume a `match` construct that behaves like Coq's `match`; here's an example, the `sum_list` from the notes linked above:

```coq title="expr"
Fixpoint sum_list (x: ref nat) (l: ilist nat) :=
  match l
  | lnil => ()
  | lcons hd tl =>
    x <- !x + hd
    let k := !tl in
    sum_list x k
  end
```

We use `Fixpoint` for clarity but this function can also be written using the recursive anonymous function $\rec{f}{x}{e}$ in the notes.

Read the program verification notes to see some (more) examples of proof outlines, especially those using pattern matching.

We will use the following _representation invariant_ for linked lists (this is a Coq definition for a separation logic proposition, except that `v` would just be a `val`; we give here its type in the expr language for clarity):

```coq
Fixpoint is_list (v: llist A) (xs: list A): hProp :=
  match x with
  | [] => v = lnil
  | hd :: x2 => ∃ tl l',
     (l = lcons hd tl) ∗
     (tl ↦ l') ∗
     is_list l' xs'
   end.
```

This definition says that `v` is the value of a linked list that holds abstract values `xs`. It relates a programming value `v`, which has references, to a purely mathematical `list`. Importantly, `is_list` is a separation logic proposition `hProp`; it only makes sense to have a linked list in some heap, since the representation involves pointers. However the mathematical part does _not_ involve pointers.

This shorthand is also useful for a reference to a linked list:

```coq
Definition is_ref_list (v: ref (llist A)) (xs: list A): hProp :=
  ∃ (p: loc) (l: llist A), (v = p) * (p ↦ l) * is_list l xs.
```

In this exercise, you'll verify this append function on linked lists. It's your job to figure out exactly how it works, in order to give a specification. Definitely look at the [program verification notes](https://gitlab.science.ru.nl/program-verification/course-2023-2024/-/blob/master/lectures/week10.md) since they include a few examples of proofs involving this implementation of linked lists and this representation predicate.

```coq title="expr"
Fixpoint app_list (l1: ref (llist A)) (l2: ref (llist A)) :=
  match !l1 with
  | lnil => l1 <- !l2; free l2; ()
  | lcons hd tl => app_list tl y
  end
```

**Exercise 5a**: write a specification for `app_list l1 l2`.

**Exercise 5b**: write a proof outline that shows `app_list l1 l2` meets your specification.

**Bonus Exercise (optional):** Find a typo in the lecture notes on Hoare logic or Separation Logic. Submit a GitHub pull request with a fix.
