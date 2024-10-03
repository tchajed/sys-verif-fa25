---
category: lecture
order: 8
shortTitle: "Lecture 8+9: Separation Logic"
---

# Lectures 8 and 9: Separation Logic

## Learning outcomes

After this lecture you should be able to

1. Predict behavior of the separating conjunction from intuition
2. Write proof outlines in separation logic
3. Appreciate the frame rule

---

<!-- @include: ./macros.snippet.md -->

## Overview

After much time spent on functional programs, we will now finally start talking about _imperative programs_. Specifically we will add mutable variables allocated on the heap and pointers. Separation logic will be the new idea that will allow reasoning about pointers, especially the problem of aliasing: two pointers might have the same value, so storing a value in one affects the other.

Separation logic is an extension of Hoare logic. We'll still have a specification of the form $\hoare{P}{e}{\fun{v} Q(v)}$. There are three main extensions:

- Our programs (the expressions $e$) will now have constructs for allocating, reading, and writing to heap memory.
- Propositions will no longer be pure and equivalent to a Coq `Prop`. Instead, they'll be predicates over the heap, of type `hProp := heap → Prop` (`heap` is our representation of the state of these imperative programs, which we'll get to later). The precondition and postcondition will be these heap predicates, so they'll say something about both program variables and the initial and final states of the program.
- In addition to the usual connectives over propositions ($P \land Q$, $P \lor Q$, $\exists x.\, P(x)$), we'll add a new _points-to assertion_ $\ell \pointsto v$ that says what the value of one heap address is, and a new _separating conjunction_ $P \sep Q$, pronounced "$P$ and separately $Q$". $P \sep Q$ says that $P$ and $Q$ both hold _separately_: they must be true over disjoint sub-parts of the heap.
- We'll add some new rules for proving separation logic triples (and keep all the old rules). A crucial rule is the _frame rule_ which permits us to write a specification for a function that talks only about the memory addresses that a program needs, while still capturing that other addresses are unchanged when we use that function's specification in a bigger context.

## Programming language

We only need a few new constructs to have something interesting:

$\text{Values}\quad v ::= \dots \mid () \mid \ell$

$\text{Expressions}\quad e ::= \dots \mid \alloc{e_1} \mid \load{e_1} \mid \store{e_1}{e_2}$

We add a value $()$ which is often called a "unit value" - you can think of it like an empty tuple, which carries no information, which will be used when a function has nothing interesting to return. Memory addresses are modeled using _locations_, which use the metavariable $\ell$. Locations are a new variant of the value type, as denoted by $v$. The type of locations will simply be `loc := Z` (unbounded mathematical integers), and we won't have a way to do pointer-integer or integer-pointer casts. A location is like the value of a pointer; it doesn't carry data, but can be dereferenced to access data.

The expression $\alloc{v}$ allocates a new location $\ell$ and gives it the initial value $v$, then reduces to $\ell$. The syntax $\load{\ell}$ is a load from the address $\ell$ while $\store{\ell}{v}$ stores $v$ in the address given by $\ell$. In all cases when these operations are used on expressions, they must first be reduced to values; loading and storing to a non-location fails (is stuck). You can think of $\load{e_1}$ as being like the C or Go code `*e1` and $\store{e_1}{e_2}$ as being like `*e1 = e2`.

The new syntax is fairly small, but it requires a big change in the semantics: programs now have state. In the computer, the heap memory is a large array of bytes. In our model of programs, it will be a little more abstract: memory addresses will be `loc := Z` (that is, mathematical and thus unbounded integers), and each location in the heap will have a value of the programming language. A heap will then be `heap := gmap loc val` or more mathematically $\Heap ::= \Loc \finto \val$; the symbol $\finto$ represents a finite partial function, which maps some locations to values, and always has a finite domain. It will be useful to talk about the _domain_ of a heap $\dom(h)$, which you can think of as the set of allocated addresses in $h$.

The semantics of a program will now be given by a new small-step operational semantics of the form $(e, h) \leadsto (e', h')$. This involves both reducing the expression $e$ and changes to a heap $h$; we will still have expressions that reduce to values. We use a new notation to be clear this is different from the _pure_ reduction step from before. I'll use $e \purestep e'$ to refer to that relation, which is still useful for many expressions since if $e \purestep e'$ then $(e, h) \leadsto (e', h)$.

### Exercise: simulate heap operations

Suppose we have a heap $h$. The locations $\ell_1$, $\ell_2$, and $\ell_3$ are allocated in $h$. Starting in $h$, the expression $\load{\ell_1}$ evalutes to $\ell_3$, $\load{\ell_2}$ evalutes to $\num{7}$, and $\load{\ell_3}$ evaluates to $\true$. We then fully evaluate the expression $\store{\load{\ell_1}}{\load{\ell_2}}$ and finish in heap $h'$. What are $h$ and $h'$?

You can use notation like $h_0 = \{\ell_1 \mapsto a, \ell_2 \mapsto b\}$ to write out a heap where $h_0(\ell_1) = a$ and $h_0(\ell_2) = b$ (and nothing else is allocated). You can also ignore any locations not mentioned.

::: details Solution

From the provided expressions, we can work out:

$$
h = \{\ell_1 \mapsto \ell_3, \ell_2 \mapsto \num{7}, \ell_3 \mapsto \true \}
$$

The three locations have different values so we can confirm they are distinct. (Did you think about that?)

The expression $\store{\load{\ell_1}}{\load{\ell_2}}$ takes several steps in $h$. It first reduces to $\store{\ell_3}{\num{7}}$, without changing the heap (though we did not say in what order those loads happen, it doesn't affect the answer). This store then results in a heap $h' = \{\ell_1 \mapsto \ell_3, \ell_2 \mapsto \num{7}, \ell_3 \mapsto \num{7}\}$.

If we choose not to ignore other locations, we can say more generally that $h = \{\ell_1 \mapsto \ell_3, \ell_2 \mapsto \num{7}, \ell_3 \mapsto \true \} \union h_f$ for some $h_f$ that does not contain $\ell_1$, $\ell_2$, or $\ell_3$, and the final heap will be $h' = \{\ell_1 \mapsto \ell_3, \ell_2 \mapsto \num{7}, \ell_3 \mapsto \num{7}\} \union h_f$ with the same $h_f$. This statement captures all the possibilities for how this example expression executes, not just the smallest heap. However, writing doesn the general statement took much more work, and this is only a one-line program; separation logic will help with that.

:::

## Heap predicates

In separation logic, when we write $\hoare{P}{e}{\fun{v} Q(v)}$, the propositions $P$ and $Q(v)$ will no longer be regular Coq `Prop`s but instead _heap predicates_ `hProp := heap → Prop`. The meaning of the Hoare triple is that if we start in an _initial heap_ where $P(h)$ is true, run $e$ till it terminates in a value $v$ and _final heap_ $h'$, then $Q(v)(h')$ holds (notice how $Q$ is a heap predicate which is a function of a value, thus it needs two arguments).

::: info Aside on logic

The view that propositions of separation logic are heap predicates is not actually necessary, and goes against traditional presentations of logic. The alternative is that propositions are _defined_ by the syntax and the rules below (plus several more rules, like the ones from the [Hoare logic section on propositions](./hoare.md#propositions)). We could then use heap predicates to give a particular "model" or semantics for what separation logic propositions mean.

As with Hoare logic, I am instead giving what's called a _model-theoretic_ view, where everything is done in the context of a specific model and all the rules are lemmas. I think this helps make things more concrete since you can think about one model rather than trying to juggle all the rules.

The logic view is still very useful. One thing it enables is that if we do proofs assuming just the rules, then we can switch to a different model where the rules are still true; while heap predicates are the standard model, there are extremely useful non-standard ones as well. Later on, when we get to concurrency, it will be practically necessary to work with the rules since the model is just too difficult to wrap your head around - someone still needs to prove the rules in that model once, but you'll be glad you're not doing it.

:::

## Separation logic propositions

$\text{Propositions}\quad P ::= \dots \mid \ell \pointsto v \mid P \sep Q \mid \emp$

The assertion $\ell \pointsto v$ (read "$\ell$ points to $v$") says that the heap maps location $\ell$ to value $v$. The proposition $P \sep Q$ (read "$P$ and separately $Q$", or simply "$P$ star $Q$") is called the _separating conjunction_. Like a regular conjunction, it asserts that both $P$ and $Q$ are true. What makes it special (and this is the key feature of separation logic) is that it also asserts $P$ and $Q$ hold in _disjoint_ parts of the heap. For example, $\ell \pointsto v \sep \ell \pointsto v$ is false, because $\ell$ cannot be allocated in two disjoint parts of the heap.

We also add a new proposition $\emp$ which says the heap is empty.

Remembering that propositions are interpreted as heap predicates, we can formally define them as follow:

_Points-to:_ The points-to connective $\ell \pointsto v$ is true for exactly one heap, which maps $\ell$ to $v$ and nothing else.

$$(\ell \pointsto v)(h) ::= h(\ell) = v \land \dom(h) = \{\ell\}$$

_Separating conjunction:_ For separating conjuction we need to say two heaps are disjoint. We could say $\dom(h) \intersect \dom(h') = \emptyset$, but it's convenient to have a shorter notation and we'll use $h \disjoint h'$:

$$(P \sep Q)(h) ::= \exists h_1, h_2.\, (h = h_1 \union h_2) \land (h_1 \disjoint h_2) \land P(h_1) \land Q(h_2)$$

::: important Understand separating conjunction

Separating conjunction is quite key to separation logic. You should make sure you understand what this definition says, with the goal of understanding it intuitively.

:::

_emp:_ This is pretty straightforward: $\emp(h) ::= h = \emptyset$ (that's the empty map). Equivalently, $\dom(h) = \emptyset$ (that's the empty set).

Here are a few rules for working with separating conjunction (the standard rules for propositions also largely apply here):

$$
\begin{aligned}
P \sep Q &\entails Q \sep P &\text{sep-comm} \\
P \sep (Q \sep R) &\entails (P \sep Q) \sep R &\text{sep-assoc} \\
(\exists x.\, P(x)) \sep Q &\entails (\exists x. \, P(x) \sep Q) &\text{sep-exists} \\
\ell \mapsto v \sep \ell \mapsto w &\entails \False &\text{pointsto-sep} \\
P &\entails P \sep \emp &\text{sep-id} \\
\end{aligned}
$$

$$
\dfrac{\lift{\phi}}{P \entails P \sep \lift{\phi}} \eqnlabel{sep-pure}
$$

$$
P \sep \lift{\phi} \entails P \eqnlabel{sep-pure-weaken}
$$

$$
\dfrac{Q \entails Q'}{P \sep Q \entails P \sep Q'} \eqnlabel{sep-monotone}
$$

Entailment between heap predicates is straightforward to define:

$P \entails Q ::= \forall (h: \Heap).\, P(h) \to Q(h)$

Remember that $P$ and $Q$ are predicates over heaps, so we cannot say one "implies" the other directly, but $P(h)$ (for some heap $h$) on the other hand is a $\mathrm{Prop}$ and we can use regular Coq implication $\to$ over it.

Remember the syntax $\lift{\varphi}$ from earlier. This "lifts" a pure proposition $\varphi : \mathrm{Prop}$ to the propositions in our logic. Before those were also $\mathrm{Prop}$ and lifting didn't do anything, but now we want heap predicates. The definition we'll choose is $(\lift{\varphi})(h) = \varphi \land h = \empty$; this requires $\varphi$ to be true and also meanwhile asserts $\varphi$ is true.

We'll also define $\True(h)$ to always be true, regardless of the heap. Observe that $\lift{\True}$ (where this True is now a pure proposition) is actually $\emp$.

### Exercise: prove sep-true

Prove $P \entails P \sep \True$, using the definitions above. (What definitions do you need?)

## Linear vs Affine separation logic

There are actually two variations on separation logic: linear and affine. What is presented above is a linear separation logic. A linear logic requires every proposition or "resource" to be used exactly once in a proof $P \entails Q$. An affine separation logic is similar, but allows propositions to be used _zero or one time_. Concretely this is due to an additional rule, a _weaken_ or _discard_ rule:

$$P \sep Q \entails P \eqnlabel{sep-weaken}$$

Typically the divide between linear and affine separation logic is that a linear logic is used for a language with manual memory management while an affine logic is used for a garbage collected language. In the linear setting we would want an operation in the language $\free{\ell}$ that deallocates the location $\ell$, which has the spec $\hoare{\ell \pointsto v}{\free{\ell}}{\emp}$. Notice that we need actual code to drop a memory address, whereas sep-weaken is a logical operation that "forgets" about memory without disposing of it in the program; in a garbage collected language this is perfectly fine, since we cannot manually dispose of memory anyway.

We will eventually want to use an affine separation logic, for two reasons:

1. We will be reasoning about Go, which is a garbage collected language.
2. In sequential linear separation logic, we can prove that if a program satisfies $\hoare{\emp}{e}{\emp}$ really deallocates all memory it uses. In concurrent separation logic, linearity does not give us this property (there are ways to leak memory while still proving the rule above). Thus there is no benefit to having linearity, while being able to discard propositions is useful.

Affine separation logic has one wrinkle, though, which is why it isn't presented as the default above. The sep-weaken rule is not compatible with the model of heap predicates above: $\ell_1 \pointsto v_1 \sep \ell_2 \pointsto v_2$ is true for a two-element heap, and $\ell_1 \pointsto v_1$ is not true in that heap (since it has too large a domain).

There are a few ways to deal with this, but the simplest to explain is also the approach taken by Iris, the implementation of (concurrent) separation logic we'll be using shortly. Instead of allowing a heap predicate to be an arbitrary function $\Heap \to \mathrm{Prop}$, we require it to be a _monotonic_ predicate $P$ where $\forall h, h'.\, P(h) \land h \disjoint h' \to P(h \union h')$. Observe that if $P$ has this property, then $P \sep Q \entails P$; we can extend the "footprint" of $P$ to include whatever memory $Q$ held over.

If you want to see a different (and more sophisticated) approach, the Software Foundations volume on Separation Logic has a [chapter on affine separation logic](https://softwarefoundations.cis.upenn.edu/slf-current/Affine.html). It makes dropping a predicate a feature of the program logic rather than the assertions themselves, and also considers that only _some_ propositions can be dropped; this allows us to, say, leak memory, but still be forced to explicitly close resources like file handles.

## Separation logic program logic rules

Now we move to the _program logic_ part of separation logic, for reasoning about programs. Separation logic adds very few rules on top of Hoare logic. First, some simple ones for the new operations:

$\hoare{\emp}{\alloc{v}}{\fun{w} \exists \ell.\, \lift{w = \ell} \sep \ell \pointsto v}%
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

The frame rule supports separation logic's _ownership reasoning_. The idea is that having an assertion in the precondition expresses "ownership", for example $\ell \pointsto v$ means the function starts out owning the location $\ell$. Owning a location means no other part of the program can read or write it. For example, in the triple $\hoare{\ell \mapsto \num{0}}{f \, (\ell, \ell')}{\funblank \ell \mapsto \num{42}}$, the function $f$ owns $\ell$ for the duration of its execution and during the proof of this triple we can be sure no other function will interfere with $\ell$. Furthermore because the triple does not mention $\ell'$ in its precondition, we know it does not need to access that location; this is what the frame rule captures.

As an example, consider proving a specification for the following program:

$$
\begin{aligned}
&e_{\text{own}} ::= \\
&\quad \lete{x}{\alloc{\num{0}}} \\ %
&\quad \lete{y}{\alloc{\num{42}}} \\ %
&\quad f \, (x, y)\then \\ %
&\quad \assert{(\load{x} == \load{y})}
\end{aligned}
$$

Assume the specification above for $f$:

$$
\hoareV{\ell \mapsto \num{0}}{f \, (\ell, \ell')}{\funblank \ell \mapsto \num{42}}
$$

::: details Definition of e1; e2 and assert

If it bothers you that we are using $e_1\then e_2$ in a program and $\assert{e}$ without defining them, here are appropriate definitions:

$e_1 \then e_2 ::= \lete{\_}{e_1} e_2$ (equivalently, a let binding with any variable unused in $e_2$)

$\assert{e} ::= \ife{e}{()}{\num{1} == \true}$ (evaluates to $()$ if $e$ is true, otherwise is an error)

What you need to know about $\operatorname{assert}$ is really just that it has the following specification:

$$\hoare{\True}{\assert{\true}}{\fun{v} \lift{v = ()}}$$.

:::

For now, we merely wish to prove that this program is safe, which means showing the assertion is always true, which is captured by the following specification:

$$\hoare{\True}{e_{\text{own}}}{\funblank \True}$$

We can give a proof outline in separation logic for this function, in the same style as we did for Hoare logic:

$$
\begin{aligned}
&\outlineSpec{\True} \\
&\quad \lete{x}{\alloc{\num{0}}} \\
&\outlineSpec{x \pointsto \num{0}} \\
&\quad \lete{y}{\alloc{\num{42}}} \\
&\outlineSpec{x \pointsto \num{0} \sep y \pointsto \num{42}} \\
&\quad f \, (x, y) \\
&\outlineSpec{x \pointsto \num{42} \sep y \pointsto \num{42}} \\
&\quad \assert{(\load{x} == \load{y})} \leadsto \\
&\quad \assert{(\load{x} == \num{42})} \leadsto \\
&\quad \assert{(\num{42} == \num{42})} \\
&\outlineSpec{x \pointsto \num{42} \sep y \pointsto \num{42}} \\
&\quad () \\
&\outlineSpec{\True} \\
\end{aligned}
$$

Some of the proof steps involve multiple operations on the same line, so I've annotated those with $\leadsto$ to indicate that we're showing how the program executes rather than a new line of code. (This is a somewhat ad-hoc notation; these proof outlines are only meant to communicate the idea of the proof to other people, so we don't need to be completely precise in what they mean.)

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

::: details Solution

$$
\begin{aligned}
&\outlineSpec{x \mapsto a \sep y \mapsto b} \\
&\quad \lete{t}{\load{x}} \\
&\outlineSpec{\lift{t = a} \sep x \mapsto a \sep y \mapsto b} \\
&\quad \store{x}{\load{y}} \leadsto \\
&\outlineSpec{\lift{t = a} \sep x \mapsto a \sep y \mapsto b} \\
&\quad \store{x}{b} \\
&\outlineSpec{\lift{t = a} \sep x \mapsto b \sep y \mapsto b} \\
&\quad \store{y}{t} \\
&\outlineSpec{\lift{t = a} \sep x \mapsto b \sep y \mapsto t} \\
&\outlineSpec{x \mapsto b \sep y \mapsto a} \\
\end{aligned}
$$

There's a frame in pretty much every step, since each line interacts with either $x$ or $y$ and the other is framed out. Technically the pure assertion $\lift{t = a}$ is also framed once it appears.

Note that at the end we can drop `\lift{t = a}` even in a linear logic; it "takes up no space" in the heap since the part where it holds also satisfies $\emp$.

:::

## Soundness

Remember that with Hoare logic, we defined what a triple means, which we called the _soundness theorem_ for Hoare logic. We also said we'll instead take it as the definition of a Hoare triple, and all the rules will be theorems proven from the definition. We can do something similar with separation logic.

At this point we should start thinking more abstractly about the logic, so we'll see four definitions of soundness, which differ in how much detail of the model (heap predicates) they rely on.

**Definition 1** _Pure Soundness_: If $\hoare{\True}{e}{\fun{v} \phi(v)}$ and $(e, h) \leadsto (e', h')$, then $(e', h')$ is not stuck, or $e' = v'$ for some value $v'$ and $\phi(v')$ holds.

This definition requires a pretty specific triple: it cannot involve anything about the heap, only a trivial precondition and a pure postcondition about the return value. However, notice that in this case it doesn't matter if we're using heap predicates or anything else.

**Definition 2** _Sequential Separation Logic Soundness_: If

$$\hoare{\bigsep_{(\ell, v) \in h_{in}} \ell \mapsto v}{e}{\fun{v} \exists h_{out}.\, \left(\bigsep_{(\ell, w) \in h_{out}} \ell \pointsto w\right) \sep \phi(v, h_{out})}$$

and $h_{in} \subseteq h$ and $(e, h) \leadsto (e', h')$, then $(e', h')$ is not stuck or $e' = v'$ for some value $v'$ and there is an $h_{out} \subseteq h'$ such that $\phi(v, h_{out})$.

This definition uses only the new separation logic propositions we've seen, points-to and separating conjunction, and also doesn't reference the fact that they are heap predicates. Notice that it does talk about framing out any extra parts of the heap not used by the precondition.

**Definition 3** _Heap predicate soundness:_ If $\hoare{P}{e}{\fun{v} Q}$ holds, if we have $P(h)$ and $(e, h) \leadsto (e', h')$, then either $(e', h')$ is not stuck, or $e' = v'$ for some value $v'$ and $Q(v')(h')$ holds.

This definition is directly given in the model with $P$ and $Q(v)$ interpreted as heap predicates.

There's a fourth definition which turns out to be especially useful:

::: info Heap predicate soundness with framing

It is convenient to define a separation logic triple to always include framing, especially if you wanted to prove the frame rule. This is one of the more useful definition of soundness. This is what that definition looks like:

**Definition 4** _Soundness with framing_: If $\hoare{P}{e}{\fun{v} Q}$ holds, if we have $P(h_1)$, some frame heap $h_f$ such that $h_1 \disjoint h_f$, and $(e, h_1 \union h_f) \leadsto (e', h')$, then $h' = h_2 \union h_f$ for some $h_2 \disjoint h_f$ and either $(e', h')$ is not stuck, or $e' = v'$ for some value $v'$ and $Q(v')(h_2)$ holds.

In this definition $h_1 \union h_f$ plays the role of $h$ and $h_2 \union h_f$ plays the role of $h'$, compared to the definitions above.

:::

## Recursion & loops {#recursion}

Imperative programs typically have loops, and we haven't yet shown a way to reason about them. As you'll see later, the ultimate goal will be to use the simple programs we have above to _model_ the behavior of an imperative program. In this process we can translate a complex feature like `for` loops into something more primitive. For all types of loops, it's sufficient to add recursion to our programming language, and a way to reason about recursive functions.

When you write a recursive function, you typically refer to the definition of the function in its body. Our language doesn't have definitions, so we instead add _recursive lambdas_ or _anonymous recursive functions_:

$$e ::= \dots \mid \rec{f}{x} e$$

The expression $\rec{f}{x} e$ is like $\fun{x} e$, except that it can call itself via the name $f$. In fact we don't need the non-recursive functions anymore; they can be replaced with new notation $\fun{x} e ::= \rec{\_}{x} e$, where we just never refer to the function recursively.

The semantics of recursive functions are given by a new and improved beta rule:

$$(\rec{f}{x} e) \, v \to e[(\rec{f}{x} e) / f][v / x]$$

We do two substitutions in a row: first, we substitute the entire original function $e$ (that's the recursion part) over the name $f$ chosen by the user, then substitute $v$ over the regular argument $x$.

We can't really use the Hoare pure-step rule to reason about this function. After using that rule, we'd come back to some recursive subcall, and we'd be in an infinite loop in the proof. The situation is much like how `destruct` isn't enough to reason about interesting theorems about `nat`; we need `induction`. The analogous reasoning here is the following rule (I've written just $Q$ as the postcondition instead of $\fun{v} Q(v)$ for concision):

$$
\dfrac{%
\hoare{P}{(\rec{f}{x} e) \, v}{Q} \entails
\hoare{P}{e[(\rec{f}{x} e) / f][v / x]}{Q}
}{%
\hoare{P}{(\rec{f}{x} e) \, v}{Q}
}
$$

If you take a moment to parse this rule, it will seem magical. In reasoning about this function, we get to assume the same triple we originally set out to prove! There are two explanations for why this works:

First, separation logic, like Hoare logic, is only giving _partial correctness_. We don't prove the function terminates, only that if it does terminate, the postcondition will be true.

Second, we get to assume the original specification only for _recursive_ occurrences; the premise has an entailment where the goal already has one step of beta reduction. In general assuming what you're about to prove is bad form (that is, allows you to prove false things), but that's not what's going on here.

We'll set aside recursion for a moment and start reasoning about loops. Let's say we want to write a function that sums the first $n$ natural numbers. We'd probably want to write it with a `for` loop. Here's one way to write it:

$$
\gdef\for{\mathrm{for}}
\begin{aligned}
&sumN ::= \\
&\quad \lete{x}{\alloc{\num{0}}} \\
&\quad \for \; \num{n} \; (\fun{i} \\
&\quad\quad \store{x}{\load{x} + i} \\
&\quad ); \\
&\quad !x
\end{aligned}
$$

The new construct $\for \; \num{n} \; f$ is equivalent to $f \, \num{0}\then f \, \num{1}\then \dots\then f \, \num{n-1}$. You can either take this as a new language feature, or expand the details block to see a definition using recursion.

::: details Defining for

On a first read it's probably useful to take for granted that $\for$ is a language construct with the expected meaning. Here's how we can put it into the language we already have (and therefore prove theorems about for loops using the recursion rule we already have):

$$
\begin{aligned}
&\for ::= \\
&\quad \fun{n, f} \\
&\quad \lete{g}{\\
&\quad\quad\begin{aligned}
&\rec{loop}{i} \\
&\quad\ife{(i = n)}{()}{f \, i\then loop \, (i + 1)} \\
\end{aligned}
} \\
&\quad g
\end{aligned}
$$

(Apologies for the formatting, still working on it.)

:::

We can prove the following rule for reasoning about for loops using a _loop invariant_ $I$ that is true when the loop starts, and is preserved by each iteration of the loop. Since the for loop always has a loop index $i$, we'll make $I$ a function of that index variable.

$$
\dfrac{
\forall (i: \mathbb{Z}).\, 0 \leq i < n \to \hoare{I(i)}{body}{I(i+1)}
}{
\hoare{I(0)}{\for \; \num{n} \; body}{I(n)}
}
$$

Using this rule, we can prove that $sumN$ returns $\num{n(n+1)/2}$. The key is to use a loop invariant $I(i) ::= x \pointsto \num{i(i+1)/2)}$.

## Magic wand (separating implication)

There is one more operator for separation logic assertions: $P \wand Q$, typically pronounced "$P$ wand $Q$". It is often affectionally called "magic wand". $P \wand Q$ is a _heap predicate_ that is true in a (sub)heap if when you add some disjoint heap satisfying $P$, the whole heap would satisfy $Q$. The wand operator is the implication of separation logic.

::: info Characterization of wand

If you remember only one thing about wand, remember $P \sep (P \wand Q) \entails Q$.

Notice the similarity to $P \land (P \to Q) \entails Q$, if we had mere $\mathrm{Prop}$s; this might help you remember this fact.

:::

Formally we can define wand as

$$(P \wand Q)(h) ::= \forall h', h \disjoint h' \to P(h) \to Q(h \union h')$$

One characterization of wand is:

$$P \entails (Q \wand R) \iff P \sep Q \entails R$$

Again, read the same thing but for propositional logic:

$$P \entails (Q \to R) \iff P \land Q \entails R$$

If you read (either of these rules) left to right, you can think of them as moving $Q$ into the hypotheses, if this were a Coq tactic. Reading right to left, we can move a hypotheses back into the goal (you haven't really needed to do that in Coq but you should certainly imagine it's sound).

There's more to say about magic wand. Some practice is needed before you become comfortable with it, which I think will be easier with the Coq development than just seeing rules on paper.

## Weakest preconditions

(The presentation here owes much to the [Separation Logic](https://softwarefoundations.cis.upenn.edu/slf-current/WPsem.html) volume of Software Foundations, written by Arthur Charguéraud)

We will now introduce weakest preconditions. The high-level view is that weakest preconditions are an alternate view on triples which have practical benefits for formalizing and automating proofs in separation logic. There's also a broader motivation to learn weakest preconditions, which is that even more automated tools for program verification like Dafny use weakest preconditions to turn the user's program, specification, and proof into a query for an SMT solver like Z3, which knows nothing about pre or postconditions.

The weakest precondition $\wp(e, Q)$, where $e$ is an expression and $Q : val \to hProp$, is a heap predicate. It is defined so that $\wp(e, Q)$ is a precondition that, if true initially, would make $Q$ a valid postcondition for $e$, and also it is the _weakest_ such precondition, more general or "better" than any other valid precondition.

We can define weakest preconditions in terms of the semantics, as a heap predicate. $\wp(e, Q)(h)$ is true if for any $e'$, $h'$ such that $(e, h) \leadsto (e', h')$, either (a) $e'$ is not stuck, or (b) $e'$ is a value $v'$ and $Q(v')(h')$.

Notice how very similar this definition is to the heap predicate soundness definition above. It is equivalent to the following (very useful) characterization:

::: info Characterization of weakest preconditions

$$
P \entails \wp(e, Q) \iff \hoare{P}{e}{Q}
$$

:::

We can reformulate this as:

$$
\left( \hoare{wp(e, Q)}{e}{Q} \right) \land %
\left( \forall P.\, \hoare{P}{e}{Q} \to P \entails \wp(e, Q) \right)
$$

The left conjunct is useful to remember: the weakest precondition is a precondition that makes $Q$ true. The right conjunct expresses the "weakest" part.

Weakest preconditions let us write more concise rules that are also better suited to automation:

$$
\dfrac{\forall v.\, Q(v) \entails Q'(v)}
{\wp(e, Q) \entails \wp(e, Q')} \eqnlabel{wp-consequence}
$$

$$
\wp(e, Q) \sep F \entails \wp(e, Q \sep F) \eqnlabel{wp-frame}
$$

One reason to introduce wand is that we can combine the frame rule and the rule of consequence into the _ramified frame rule_:

$$
\wp(e, Q) \sep (\forall v.\, Q(v) \wand Q'(v)) \entails \wp(e, Q') \eqnlabel{wp-ramified-frame}
$$

Weakest preconditions also make for more concise rules about sequencing and bind:

$$
\wp(e_1, (\fun{v} \wp(e_2, Q))) \entails \wp((e_1\then e_2), Q) \eqnlabel{wp-seq}
$$

This is a special case of bind. Exercise: extend it to an arbitrary evaluation context, following the template of the Hoare bind rule.

Notice how unlike the hoare-seq rule, we don't have to invent an intermediate condition that is true after $e_1$; it's implicit that we can prove any postcondition that implies $\wp(e_2, Q)$ - this is the power of using a definition of _weakest_ precondition.
