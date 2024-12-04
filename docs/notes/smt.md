---
category: lecture
order: 25
shortTitle: "Lecture 25: SMT verification"
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Lecture 25: Automated verification with SMT

In this lecture we'll talk about verifying sequential programs with Hoare logic, but with a high degree of automation using an SMT solver.

## Learning outcomes

1. Explain what a specification means in an SMT-based tool like Dafny.
2. Translate between the Coq and Dafny styles of proofs.

---

<!-- @include: ./macros.snippet.md -->

$$
\gdef\add{\operatorname{add}}
$$

## Motivation

It can be tedious to write proofs in Coq. Luckily, there are more automated approaches to verification which leverage sophisticated solvers to reduce the proof burden. However, automated verification isn't a solution to all your problems: there are limits to what can be efficiently automatically proven, and in practice the developer still needs to help the solver to prove correct programs. Automation is also more specialized, limiting what programs you can verify, especially when it comes to separation logic and concurrency, and going beyond current tools into research territory. Extending the reach of automation is an active area of research.

## Recall: sequential proofs without separation logic

Remember that we did sequential proofs in a _Hoare outline_ style even before we started using separation logic. These outlines had lines of code separated by an assertion that we know holds at that point in the code, starting with the precondition (assumed to be true) and ending with the postcondition (the final outcome of the proof).

Here is an example we saw before. The code we want to verify is $f$, implemented with helper functions $\add$ and $\min$:

$$
\begin{aligned}
\add &= \lambda x, y.\, x + y \\
\min &= \lambda x, y.\, \ife{x < y}{x}{y} \\
\operatorname{f} &= \fun{x} \add \, (\min \, 0 \, x) \, 1 \\
\end{aligned}
$$

Assume we have specifications for the helper functions (remember that these are intentionally not the most general specification possible):

$$
\hoare{n + m < 2^{64}}%
{\add \, \overline{n} \, \overline{m}}%
{\fun{v} v = \overline{n + m}}
$$

$$
\hoare{\True}%
{\min \, \overline{n} \, \overline{m}}%
{\fun{v} \exists (p: \mathbb{Z}).\, v = \overline{p} \land p \leq n \land p \leq m }
$$

Now we'll prove a specification for $f$ with this Hoare outline:

$$
\begin{aligned}
&\outlineSpec{n < 2^{64} - 1} \\
&\outlineSpec{\True} \\
&\quad \lete{m}{\min \, 0 \, \overline{n}} \\
&\outlineSpec{\exists p_m.\, m = \overline{p_m} \land p_m \leq 0 \land p_m \leq n} \\
&\quad \lete{y}{\operatorname{add} \, m \, 1} \\
&\outlineSpec{y = \overline{p_m + 1}} \\
&\quad y \\
&\outlineSpec{\exists (p: \mathbb{Z}).\, y = \overline{p} \land p \leq 1)}
\end{aligned}
$$

## Dafny specifications and functions

Dafny is a **verification-oriented programming language**. It has functionality for implementation, specification, and proof all in the same language.

We write the implementations in a language inspired by C#, with the usual imperative features as well as object-oriented features like classes (but not inheritance like in C# and Java). Imperative code is written as `method`s in Dafny. To run the code, Dafny includes a compiler which supports a number of backends, including C#, Java, and Go, which we then link with other code and compile with the language's toolchain.

Specifications are written with pre- and post-conditions attached to methods with the `requires` and `ensures` keywords. Dafny's specification language supports rich functional programs using mathematical data types like `int` (unbounded integers) and `seq<T>` (mathematical sequences), similar to what you saw in Coq before we started verifying imperative programs.

Method specifications are checked mostly automatically by a solver (which we'll talk about shortly), but Dafny also has features for writing proofs to assist the solver when it can't do the proof on its own.

## Example proof

Here's the example above, translated to a Dafny proof (the definition of `INT_MAX` has been omitted):

```dafny
method Add(x: int, y: int) returns (z: int)
  requires x + y <= INT_MAX
  ensures z == x + y
{
  return x + y;
}

method Min(x: int, y: int) returns (z:int)
  ensures z <= x && z <= y
{
  if x < y {
    return x;
  } else {
    return y;
  }
}

method F(n: int) returns (z: int)
  requires n < INT_MAX
  ensures z <= 1
{
  var m := Min(0, n);
  var y := Add(m, 1);
  return y;
}
```

Sometimes need to give some help to verifier with `assert` and `if`:

```dafny
function seq_sum(s: seq<int>): int
{
  if s == [] then 0
  else s[0] + seq_sum(s[1..])
}

lemma seq_sum_app(s1: seq<int>, s2: seq<int>)
  ensures seq_sum(s1 + s2) == seq_sum(s1) + seq_sum(s2)
{
  if s1 == [] {
    assert s1 + s2 == s2;
    return;
  }
  seq_sum_app(s1[1..], s2);
  assert s1[1..] + s2 == (s1 + s2)[1..];
}
```

## Writing Dafny proofs

The challenge you face when a Dafny proof doesn't go through is what to do (or how to find an error in your code or specification). In Coq, we had a goal and tactics slowly manipulated that goal. Dafny does not have such an explicit "current goal" nor a context of all the facts you have to work with like the Coq context.

The process of writing a Dafny proof involves a feedback loop between seeing a Dafny error, decoding what Dafny is and isn't able to prove, writing some assertion or other part of the proof, then seeing how this changes the error. The feedback loop both helps you write the proof (e.g., you add an assertion and this makes the proof go through) and gets you more information about what the solver _can_ prove and what remains.

If you're actually working on a Dafny proof, you should read the [Verification section](https://dafny.org/dafny/DafnyRef/DafnyRef#sec-verification) of the Dafny reference manual, which walks through a number of strategies for figuring out why a proof is failing. We'll demo some of these techniques on the `seq_sum_app` proof above.

## How Dafny works

The basic idea is that Dafny converts your code, specification, and proof into a big formula (using weakest preconditions), and then checks if that formula is always true using a powerful logic solver. What Dafny is doing is translating everything related to programs - like code, loop invariants, and the meaning of pre- and post-conditions - into something simpler that the solver understands.

### SMT solver

The solver in question is an SMT solver, which stands for "satisfiability modulo theories". The most commonly used SMT solver is Z3, and this is the only solver Dafny supports (currently).

To understand what an SMT solver does, it helps to start by thinking about SAT solvers ("satisfiability", without the "theories" of SMT). You give a SAT solver a question like "if we have boolean variables $a$, $b$, $c$, is there some assignment of values to those variables that makes $(a \lor b) \land (c \lor \lnot b)$ true?" and it responds with SAT and (optionally) tells you $a = \mathrm{true}$ and $c = \mathrm{true}$ makes the formula true ($b$ doesn't matter). On the other hand if you ask if $(a \lor b) \land (\lnot c \lor \lnot b) \land (b \lor \lnot a)$ then it responds UNSAT because there is no satisfying assignment.

An SMT solver extends the SAT paradigm with _theories_ like arithmetic: we can add variables that aren't booleans, and we can use standard operators like + and < with the usual meanings. We can also have quantifiers (forall and exists) in our formulas. Still, the SMT solver aims to either give a satisfying assignment or determine that that the formula is UNSATisfiable.

### Weakest preconditions

Basic idea: compute a formula `WP(body, post)` for some method. Ask SMT solver if there exist values such that `!(pre ==> WP(body, post))`. If it says SAT, then `{pre} body {post}` does not hold (we have a bug). If it says UNSAT then `pre ==> WP(body, post)` and specification holds.

How to compute the WP of an expression? Mostly we can follow inference rules we've already seen for Hoare logic, but it takes a little work to turn this into an algorithm. See chapter 2 of _Program Proofs_ by K. Rustan M. Leino (the creator of Dafny) for an excellent detailed explanation.

#### Variable assignment

Let's do some concrete examples and then see the general rule. For each exercise, fill in the `?` with the weakest precondition (that is, make the specification as general as possible):

**Exercise 1:** `{{ ? }} y := a + b {{ 25 <= y }}`

**Exercise 2:** `{{ ? }} a := x + 3 {{ 25 <= a + 12 }}`

**Exercise 3:** `{{ ? }} x := x + 1 {{ x <= y }}`

In general, $\mathit{WP}(\mathtt{x := E}, Q) = Q[x := E]$ where $Q[x := E]$ denotes substituting $E$ for every occurrence of the variable $x$ in the formula $Q$.

#### If statements

Consider `if B then { T } else { U }`.

(TODO: add pictorial version to notes)

$$
\mathit{WP}(\text{\texttt{if B then \{ T \} else \{ U \}}}, Q) =\\
(B \implies \mathit{WP}(T, Q)) \land (\lnot B \implies \mathit{WP}(U, Q))
$$

#### Exercise

What's the weakest precondition for this expression, with the given postcondition?

```txt
{{ ? }}
if x < 3 { x, y := x + 1, 10 } else { y := x }
{{ x + y == 100 }}
```

(What do you think the weakest precondition for the _simultaneous assignment_ `x, y := x + 1, 10` should be?)

#### Putting it all together

```dafny
method Triple(q: int) returns (r: int)
  requires 3 < q
  ensures r == q * 3
{
  if q < 5 {
    r := 12;
  } else {
    r := q * 2;
    r := r + q;
  }
}
```

The corresponding verification condition (hand written, not the actual Dafny output) involves computing the weakest precondition with respect to the `ensures` clause, and then asserting that it does _not_ hold that the precondition implies the weakest precondition. Remember that if this overall formula is unsatisfiable the specification is correct, and otherwise there is a bug.

```smt2
;; this declares q as a constant (a function with no arguments) of type int,
;; to represent an arbitrary input to Triple
(declare-fun q () Int)

(assert (not ;; this not negates the overall (pre ==> WP(body, post))
         (let ((b1 (=>
                    (< q 5)
                    ; 12 = q * 3
                    (= 12 (* q 3))))
               (b2 (=>
                    (not (< q 5))
                    ;; q * 2 + q = q * 3
                    (= (+ (* q 2) q) (* q 3)))))
           (=> (< 3 q) (and b1 b2)))
         ))
(check-sat)
```

**Exercise:** Within this expression, what part is the weakest precondition of the postcondition?

## Problems with SMT solving

The fact that verification is undecidable means some queries (generated verification conditions) will be too difficult and the solver will take too long or go into an infinite loop. In that case the user gets a timeout rather than SAT or UNSAT, leading to an inconclusive result.

One core issue with SMT solving is _triggers_. Triggers are how the SMT solver decides to use a forall quantifier, and how it picks a witness to prove an exists.

## Limitations

Dafny does not support concurrency. It has a solution different from separation logic for dealing with aliasing - dynamic frames.

[Viper](https://www.pm.inf.ethz.ch/research/viper.html) uses weakest preconditions, but with separation logic. But this means `pre ==> WP(body, post)` is a separation logic entailment, which is harder to solve (it's no longer something supported by Z3), so Viper also has to implement a custom solver.

Newer tools like [Verus](https://github.com/verus-lang/verus) (like Dafny but for Rust) have added preliminary support for concurrent verification based on Iris ghost state, and use Rust to handle aliasing and mutability instead of separation logic. However Iris is still (currently) the most advanced tool for reasoning about concurrency.

All automated tools bake-in some particular approach and inherit the limitations of the solver. Due to [Iris](https://iris-project.org/) being more _foundational_ it's possible to extend it in fundamental ways (reasoning about new programs and new specifications) - see the long list of papers on the Iris website, many of which are extensions of the core theory. Usability of interactive proofs will probably never be as good as automation; an active area of research is extending automation to these new proofs and specifications.
