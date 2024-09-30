---
category: lecture
order: 8
---

# Lecture 8: Separation logic

## Learning outcomes

After this lecture you should be able to

1. Predict behavior of the separating conjunction from intuition
2. Write proof outlines in separation logic
3. Appreciate the frame rule

---

## Overview

After much time spent on functional programs, we will now finally start talking about _imperative programs_. Specifically we will add mutable variables allocated on the heap and pointers. Separation logic will be the new idea that will allow reasoning about pointers, especially the problem of aliasing: two pointers might have the same value, so storing a value in one affects the other.

$$
\gdef\ife#1#2#3{\text{\textbf{if} } #1 \text{ \textbf{then} } #2 \text{ \textbf{else} } #3}
\gdef\lete#1#2{\text{\textbf{let} } #1 := #2 \text{ \textbf{in} }}
\gdef\letV#1#2{&\text{\textbf{let} } #1 := #2 \text{ \textbf{in} }}
\gdef\true{\mathrm{true}}
\gdef\True{\mathrm{True}}
\gdef\False{\mathrm{False}}
\gdef\false{\mathrm{false}}
\gdef\hoare#1#2#3{\left\{#1\right\} \, #2 \, \left\{#3\right\}}
\gdef\hoareV#1#2#3{\begin{aligned}%
&\left\{#1\right\} \\ &\quad #2 \\ &\left\{#3\right\}%
\end{aligned}}
\gdef\outlineSpec#1{\left\{#1\right\}}
\gdef\fun#1{\lambda #1.\,}
\gdef\funblank{\fun{\_}}
\gdef\rec#1#2{\text{\textbf{rec} } #1 \, #2.\;}
\gdef\app#1#2{#1 \, #2}
\gdef\then{;\;}
\gdef\entails{\vdash}
\gdef\eqnlabel#1{\:\:\text{#1}}
\gdef\lift#1{\lceil #1 \rceil}

\gdef\sep{\mathbin{\raisebox{1pt}{$\star$}}}
%\gdef\load#1{\operatorname{Load}(#1)}
%\gdef\store#1#2{\operatorname{Store}(#1, #2)}
\gdef\load#1{{!}\,#1}
\gdef\store#1#2{#1 \mathbin{\gets} #2}
\gdef\alloc#1{\operatorname{alloc} \, #1}
\gdef\assert#1{\operatorname{assert} \, #1}
\gdef\purestep{\xrightarrow{\text{pure}}}
\gdef\intersect{\cap}
\gdef\union{\cup}

\gdef\pointsto{\mapsto}
\gdef\disjoint{\mathrel{\bot}}
\gdef\Heap{\mathrm{Heap}}
\gdef\Loc{\mathrm{loc}}
\gdef\val{\mathrm{val}}
\gdef\finto{\overset{\text{fin}}{\rightharpoonup}}
\gdef\dom{\operatorname{dom}}
$$

Separation logic is an extension of Hoare logic. We'll still have a specification of the form $\hoare{P}{e}{\fun{v} Q(v)}$. There are three main extensions:

- Our programs (the expressions $e$) will now have constructs for allocating, reading, and writing to heap memory.
- Propositions will no longer be pure and equivalent to a Coq `Prop`. Instead, they'll be predicates over the heap, of type `hProp := heap → Prop` (`heap` is our representation of the state of these imperative programs, which we'll get to later). The precondition and postcondition will be these heap predicates, so they'll say something about both program variables and the initial and final states of the program.
- In addition to the usual connectives over propositions ($P \land Q$, $P \lor Q$, $\exists x.\, P(x)$), we'll add a new _separating conjunction_ $P \sep Q$. We'll start using the notation $\lift{\phi}$ ("lift phi"), which takes an ordinary `Prop` and turns it into an `hProp`. It'll be more important to distinguish these pure propositions because once true, they remain true, whereas a statement about the state of the program can become false as the state evolves.
- We'll add some new rules for proving separation logic triples (and keep all the old rules).

## Programming language

We only need a few new constructs to have something interesting:

$\text{Values}\quad v ::= \dots \mid () \mid \ell$

$\text{Expressions}\quad e ::= \dots \mid \alloc{e_1} \mid \load{e_1} \mid \store{e_1}{e_2}$

We add a value $()$ which is often called a "unit value" - you can think of it like an empty tuple, which carries no information, which will be used when a function has nothing interesting to return. Memory addresses are modeled using _locations_, which use the metavariable $\ell$. Locations are a new variant of the value type, as denoted by $v$. The type of locations will simply be `loc := Z` (unbounded mathematical integers), and we won't have a way to do pointer-integer or integer-pointer casts. A location is like the value of a pointer; it doesn't carry data, but can be dereferenced to access data.

The expression $\alloc{v}$ allocates a new location $\ell$ and gives it the initial value $v$, then reduces to $\ell$. The syntax $\load{\ell}$ is a load from the address $\ell$ while $\store{\ell}{v}$ stores $v$ in the address given by $\ell$. In all cases when these operations are used on expressions, they must first be reduced to values; loading and storing to a non-location fails (is stuck). You can think of $\load{e_1}$ as being like the C or Go code `*e1` and $\store{e_1}{e_2}$ as being like `*e1 = e2`.

The new syntax is fairly small, but it requires a big change in the semantics: programs now have state. In the computer, the heap memory is a large array of bytes. In our model of programs, it will be a little more abstract: memory addresses will be `loc := Z` (that is, mathematical and thus unbounded integers), and each location in the heap will have a value of the programming language. A heap will then be `heap := gmap loc val` or more mathematically $\Heap ::= \Loc \finto \val$; the symbol $\finto$ represents a finite partial function, which maps some locations to values, and always has a finite domain. It will be useful to talk about the _domain_ of a heap $\dom(h)$, which you can think of as the set of allocated addresses in $h$.

The semantics of a program will now be given by a new small-step operational semantics of the form $(e, h) \leadsto (e', h')$. This involves both reducing the expression $e$ and changes to a heap $h$; we will still have expressions that reduce to values. We use a new notation to be clear this is different from the _pure_ reduction step from before. I'll use $e \purestep e'$ to refer to that relation, which is still useful for many expressions since if $e \purestep e'$ then $(e, h) \leadsto (e', h)$.

### Exercise: simulate heap operations

Suppose we have a heap $h$. The locations $\ell_1$, $\ell_2$, and $\ell_3$ are allocated in $h$. Starting in $h$, the expression $\load{\ell_1}$ evalutes to $\ell_3$, $\load{\ell_2}$ evalutes to $\overline{7}$, and $\load{\ell_3}$ evaluates to $\true$. We then fully evaluate the expression $\store{\load{\ell_1}}{\load{\ell_2}}$ and finish in heap $h'$. What are $h$ and $h'$?

You can use notation like $h_0 = \{\ell_1 \mapsto a, \ell_2 \mapsto b\}$ to write out a heap where $h_0(\ell_1) = a$ and $h_0(\ell_2) = b$ (and nothing else is allocated). You can also ignore any locations not mentioned.

## Heap predicates

In separation logic, when we write $\hoare{P}{e}{\fun{v} Q(v)}$, the propositions $P$ and $Q(v)$ will no longer be regular Coq `Prop`s but instead _heap predicates_ `hProp := heap → Prop`. The meaning of the Hoare triple is that if we start in an _initial heap_ where $P(h)$ is true, run $e$ till it terminates in a value $v$ and _final heap_ $h'$, then $Q(v)(h')$ holds (notice how $Q$ is a heap predicate which is a function of a value, thus it needs two arguments).

::: info Aside on logic

The view that propositions of separation logic are heap predicates is not actually necessary, and goes against traditional presentations of logic. The alternative is that propositions are _defined_ by the syntax and the rules below (plus several more rules, like the ones from the [Hoare logic section on propositions](./hoare.md#propositions)). We could then use heap predicates to give a particular "model" or semantics for what separation logic propositions mean.

As with Hoare logic, I am instead giving what's called a _model-theoretic_ view, where everything is done in the context of a specific model and all the rules are lemmas. I think this helps make things more concrete since you can think about one model rather than trying to juggle all the rules.

The logic view is still very useful. One thing it enables is that if we do proofs assuming just the rules, then we can switch to a different model where the rules are still true; while heap predicates are the standard model, there are extremely useful non-standard ones as well. Later on, when we get to concurrency, it will be practically necessary to work with the rules since the model is just too difficult to wrap your head around - someone still needs to prove the rules in that model once, but you'll be glad you're not doing it.

:::

## Separation logic propositions

$\text{Propositions}\quad P ::= \dots \mid \ell \pointsto v \mid P \sep Q$

The assertion $\ell \pointsto v$ (read "$\ell$ points to $v$") says that the heap maps location $\ell$ to value $v$. The proposition $P \sep Q$ (read "$P$ and separately $Q$", or simply "$P$ star $Q$") is called the _separating conjunction_. Like a regular conjunction, it asserts that both $P$ and $Q$ are true. What makes it special (and this is the key feature of separation logic) is that it also asserts $P$ and $Q$ hold in _disjoint_ parts of the heap. For example, $\ell \pointsto v \sep \ell \pointsto v$ is false, because $\ell$ cannot be allocated in two disjoint parts of the heap.

Remembering that propositions are interpreted as heap predicates, we can formally define them as follow:

_Points-to:_ The points-to connective $\ell \pointsto v$ is true for exactly one heap, which maps $\ell$ to $v$ and nothing else.

$$(\ell \pointsto v)(h) ::= h(\ell) = v \land \dom(h) = \{\ell\}$$

_Separating conjunction:_ For separating conjuction we need to say two heaps are disjoint. We could say $\dom(h) \intersect \dom(h') = \emptyset$, but it's convenient to have a shorter notation and we'll use $h \disjoint h'$:

$$(P \sep Q)(h) ::= \exists h_1, h_2.\, (h = h_1 \union h_2) \land (h_1 \disjoint h_2) \land P(h_1) \land Q(h_2)$$

::: important Understand separating conjunction

Separating conjunction is quite key to separation logic. You should make sure you understand what this definition says, with the goal of understanding it intuitively.

:::

The rules for working with separating conjunction have parts that are quite intuitive and some that are surprising:

$$
\begin{aligned}
P \sep Q &\entails P &\text{sep-weaken}\\
P &\entails P \sep \True &\text{sep-true} \\
P \sep Q &\entails Q \sep P &\text{sep-comm} \\
P \sep (Q \sep R) &\entails (P \sep Q) \sep R &\text{sep-assoc} \\
(\exists x.\, P(x)) \sep Q &\entails (\exists x. \, P(x) \sep Q) &\text{sep-exists} \\
\ell \mapsto v \sep \ell \mapsto w &\entails \False &\text{pointsto-sep} \\
\end{aligned}
$$

The two surprising rules are $P \sep Q \entails P$ and $P \entails P \sep \True$. These are desirable rules, but we have to be careful for them to be true. For the first, $P \sep Q \entails P$, we define entailment in a non-obvious way:

$P \entails Q ::= \forall h.\, P(h) \to \exists h_1, h_2.\, (h = h_1 \union h_2) \land Q(h_1)$

What this says is that $P \entails Q$ can be true if $P(h)$ implies that $Q$ holds not on the whole heap but just a _sub-heap_ $h_1$. This definition is chosen precisely so that the sep-weaken rule is true, and it permits us to prove implications in separation logic that "forget" conjuncts. This is actually similar to how normal conjunction works (the fact that $P \land Q \entails P$ doesn't surprise anyone).

For $P \entails P \sep \True$, we'll come back to the syntax $\lift{\varphi}$ we saw earlier. This "lifts" a pure proposition $\varphi : \mathrm{Prop}$ to the propositions in our logic. Before those were also $\mathrm{Prop}$ and this didn't do anything, but now we want heap predicates. The definition we'll choose is $(\lift{\varphi})(h) = \varphi$ - a lifted proposition is true for any heap, as long as $\varphi$ holds in general. Now we define $\True = \lift{\True}$ (we are overloading the syntax, sorry); this makes $P \entails P \sep \True$ true, as you'll prove.

### Exercise: prove sep-true

Prove $P \entails P \sep \True$, using the definitions above. (What definitions do you need?)

## Separation logic proof rules

Separation logic adds very few rules. First, some simple ones for the new operations:

$\hoare{True}{\alloc{v}}{\fun{w} \exists \ell.\, \lift{w = \ell} \sep \ell \pointsto v}%
\eqnlabel{alloc-spec}$

$\hoare{\ell \pointsto v}{\load{\ell}}{\fun{w} \lift{w = v} \sep \ell \pointsto v}%
\eqnlabel{load-spec}$

$\hoare{\ell \pointsto v_0}{\store{\ell}{v}}{\funblank \ell \pointsto v}%
\eqnlabel{store-spec}$

These are not that surprising. These rules are sometimes called the "small footprint axioms" because they only talk about the smallest part of the heap that is relevant to the operation. We add a bit of notation here: $\funblank$ is used for a postcondition that ignores the return value.

The heart of separation logic is the celebrated **frame rule**:

$\dfrac{\hoare{P}{e}{\fun{v} Q(v)}}%
{\hoare{P \sep F}{e}{\fun{v} Q(v) \sep F}} \eqnlabel{frame}%
$

The frame rule supports separation logic's _ownership reasoning_. The idea is that having an assertion in the precondition expresses "ownership", for example $\ell \pointsto v$ means the function starts out owning the location $\ell$. Owning a location means no other part of the program can read or write it. For example, in the triple $\hoare{\ell \mapsto \overline{0}}{f \, (\ell, \ell')}{\funblank \ell \mapsto \overline{42}}$, the function $f$ owns $\ell$ for the duration of its execution and during the proof of this triple we can be sure no other function will interfere with $\ell$. Furthermore because the triple does not mention $\ell'$ in its precondition, we know it does not need to access that location; this is what the frame rule captures.

As an example, consider proving a specification for the following program:

$$
\begin{aligned}
&e_{\text{own}} ::= \\
&\quad \lete{x}{\alloc{\overline{0}}} \\ %
&\quad \lete{y}{\alloc{\overline{42}}} \\ %
&\quad f \, (x, y)\then \\ %
&\quad \assert{(\load{x} == \load{y})}
\end{aligned}
$$

::: details Definition of e1; e2 and assert

If it bothers you that we are using $e_1\then e_2$ in a program and $\assert{e}$ without defining them, here are appropriate definitions:

$e_1 \then e_2 ::= \lete{\_}{e_1} e_2$ (equivalently, a let binding with any variable unused in $e_2$)

$\assert{e} ::= \ife{e}{()}{\overline{1} == \true}$ (evaluates to $()$ if $e$ is true, otherwise is an error)

What you need to know about $\operatorname{assert}$ is really just that it has the following specification:

$$\hoare{\True}{\assert{\true}}{\fun{v} \lift{v = ()}}$$.

:::

For now, we merely wish to prove that this program is safe, which means showing the assertion is always true, which is captured by the following specification:

$$\hoare{\True}{e_{\text{own}}}{\funblank \True}$$

We can give a proof outline in separation logic for this function, in the same style as we did for Hoare logic:

$$
\begin{aligned}
&\outlineSpec{\True} \\
&\quad \lete{x}{\alloc{\overline{0}}} \\
&\outlineSpec{x \pointsto \overline{0}} \\
&\quad \lete{y}{\alloc{\overline{42}}} \\
&\outlineSpec{x \pointsto \overline{0} \sep y \pointsto \overline{42}} \\
&\quad f \, (x, y) \\
&\outlineSpec{x \pointsto \overline{42} \sep y \pointsto \overline{42}} \\
&\quad \assert{(\load{x} == \load{y})} \\
&\outlineSpec{x \pointsto \overline{42} \sep y \pointsto \overline{42}} \\
&\quad \assert{(\overline{42} == \load{y})} \\
&\outlineSpec{x \pointsto \overline{42} \sep y \pointsto \overline{42}} \\
&\quad \assert{(\overline{42} == \overline{42})} \\
&\outlineSpec{x \pointsto \overline{42} \sep y \pointsto \overline{42}} \\
&\quad () \\
&\outlineSpec{\True} \\
\end{aligned}
$$

### Exercise: prove swap correct

$$
\operatorname{swap} \, \ell_1 \, \ell_2 ::=
\lete{t}{\load{\ell_1}} %
\store{\ell_1}{\load{\ell_2}}\then \store{\ell_2}{t}
$$

$$
\hoareV{x \pointsto a \sep y \pointsto b}%
{\operatorname{swap} \, x \, y}%
{\funblank x \pointsto b \sep y \pointsto a}
$$

You should write out swap as three lines of code for this outline. Identify what the frame $F$ is each time your outline (implicitly) uses the frame rule.

::: info Hint

Recall that from one assertion to the next is supposed to use a known specification for the function in between (for the outline to be valid). When you have more facts in the precondition than the known specification, you need to use the frame rule.

:::

## Recursion

::: warning Draft

From this point forward these notes are still a draft.

:::

Imperative programs typically have loops, and we haven't yet shown a way to reason about them. As you'll see later, the ultimate goal will be to use the simple programs we have above to _model_ the behavior of an imperative program. In this process we can translate a complex feature like `for` loops into something more primitive. For all types of loops, it's sufficient to add recursion to our programming language, and a way to reason about recursive functions.

When you write a recursive function, you typically refer to the definition of the function in its body. Our language doesn't have definitions, so we instead add _recursive lambdas_ or _anonymous recursive functions_:

$$e ::= \dots \mid \rec{f}{x} e$$

The expression $\rec{f}{x} e$ is like $\fun{x} e$, except that it can call itself via the name $f$. In fact we don't need the non-recursive functions anymore; they can be replaced with notation $\fun{x} e ::= \rec{\_}{x} e$, where we just never refer to the function recursively.

## Weakest preconditions

What we've seen so far as separation logic rules that can form a full proof, but they were cumbersome to use, so we've instead been verifying programs with proof outlines. The proof outlines are a useful way to think about the proof, but hard to formalize in a way that captures all the obligations (and they don't handle capture uses of the bind rule).

Weakest preconditions will solve both of these problems: we'll have a fully formal way of using the logic's rules while also being able to manage a proof in practice (and in particular in Coq).
