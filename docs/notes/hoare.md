---
category: lecture
order: 5
---

# Lecture 6: Hoare Logic

## Introduction

### Learning outcomes

1. Understand how a small-step operational semantics explains what a program does.
2. Explain what a Hoare triple means.
3. Use Hoare logic rules to prove (simple) programs on paper.

---

We have so far taken a view of program verification where the code is a functional program in Coq, the specification is a property about that function (we a style of writing these properties where an ADT is related to a model), and the proof uses any Coq-level reasoning required.

We will now develop Hoare logic, a formal system for reasoning about program correctness. At first, the code will still be functional programs. The specifications will use a new style of pre- and post-conditions, attached to each function. Proofs will use the rules of Hoare logic to handle each programming feature and to compose existing specifications together. Hoare logic will provide a smooth path to separation logic and concurrent separation logic, which add extensions for reasoning about more interesting programs while retaining much of the basic structure of this simple version.

::: important Reading these notes

These lecture notes are written in a bottom-up style: each definition is presented in detail, then used later. This is intended to be a good reference but is not ideal for reading in order. It is not the order the live lecture is presented in.

When reading the notes, I suggest reading the introduction in each sub-section, then moving forward, until you get to the Hoare logic subsection. You can go back if you ever need to understand something in more detail or to see a specific rule or definition.

:::

Hoare logic and its extensions are the basis of a good deal of program reasoning, including more semi-automated verification tools like Dafny and F\*, as well as the Iris framework we will use in this class. The general setup is that the user writes pre- and post-conditions in the source code and then some form of automation kicks in to prove that those annotations are correct. The purpose of learning Hoare logic itself rather than starting with verifying programs is to understand more deeply two things:

1. What does it mean to have a "verified" program annotated with pre- and post-conditions when the verification succeeds?
2. When a proof fails, what reasoning are tools following?

The second question is especially important since you will face failed proofs in verification (either because of incorrect code, incorrect specifications, or because the proof isn't done), and it is extremely helpful to have a good mental model of what's going on when debugging them.

## Programming language

We'll start by defining a programming language and its semantics. The goal right now is to have just enough features to understand the rules of Hoare logic; eventually we'll add features to enable writing useful programs, without changing the structure of the verification features.

### Syntax

The language is an extension of the $\lambda$-calculus that includes tuples, numbers and booleans as primitive data, and arithmetic operations for addition and comparison.

<!--
\gdef is like \def but defines a command in the global KaTeX context, for
subsequent math blocks.
-->

$$
\gdef\ife#1#2#3{\operatorname{if} #1 \operatorname{then} #2 \operatorname{else} #3}
\gdef\lete#1#2#3{\operatorname{let} #1 := #2 \operatorname{in} #3}
\gdef\true{\mathrm{true}}
\gdef\True{\mathrm{True}}
\gdef\false{\mathrm{false}}
\gdef\hoare#1#2#3{\{#1\} \, #2 \, \{#3\}}
\gdef\fun#1{\lambda #1.\,}
\gdef\app#1#2{#1 \, #2}
\gdef\app#1#2{#1 \, #2}
\gdef\entails{\vdash}
\gdef\eqnlabel#1{\:\:\text{#1}}
$$

$$
\newcommand{\linecontinue}{\phantom{::=}}
\begin{aligned}
&\mathrm{Expressions} &e &::= x \mid v \mid \fun{x} e \mid \app{e_1}{e_2} \\
&&&\linecontinue \mid \ife{e}{e_1}{e_2} \\
&&&\linecontinue \mid e_1 + e_2 \mid e_1 == e_2 \mid e_1 < e_2 \\
&&&\linecontinue \mid (e_1, e_2) \mid \pi_1 \, e \mid \pi_2 \, e \\
&\mathrm{Values} &v &::= \lambda x.\, e \mid \overline{n} \mid \mathrm{true} \mid \mathrm{false} \mid (v_1, v_2)
\end{aligned}
$$

Common syntactic sugar:

$$
\begin{aligned}
\fun{x, y} e &::= \fun{x} \fun{y} e \\
\lete{x}{e_1}{e_2} &::= (\fun{x} e_2) \, e_1 \\
\app{\app{e_1}{e_2}}{e_3} &::= \app{(\app{e_1 \, e_2})}{e_3}
\end{aligned}
$$

Some notation is worth explaining here. The production $e ::= x$ says that a variable like $x$ or $y$ is an expression ($e$ in the grammar). $e ::= v$ says that any value (defined above) can also be used as an expression. $v ::= \overline{n}$ says that an integer constant $\overline{n}$ is a value; the overline is used to distinguish numbers in the syntax $n$ vs numbers in the meta language $\overline{n}$.

::: warning If you've seen the λ-calculus before...

You may have seen a definition of the lambda calculus that basically said $e ::= x \mid v \mid \fun{x} e$. Separately, you would then have a definition of a value predicate $\operatorname{val}(e)$ (probably as part of the semantics), defined so that only lambda abstractions are values.

The definition above instead makes values a separate syntax, and then embeds them into expressions. A value is only the expressions formed this way. When this definition is formalized in Coq, this does mean that there are some constructs like pairs and lambda abstractions that appear in both the definition of expressions and values, but we can be ambiguous via an "abuse of notation" when working on paper.

:::

The language may look too primitive to do anything if you haven't seen a presentation of the $\lambda$-calculus before; the examples below should help. The main thing we can do is to define functions using the $\fun{x} e$ construct, which is a _lambda abstraction_ or _anonymous function_. The syntax $e_1 \, e_2$ for _application_ is used when $e_1$ is a function to apply it to $e_2$.

Examples of functions:

$$
\begin{aligned}
\operatorname{add} &= \lambda x, y.\, x + y \\
\operatorname{and} &= \lambda b_1, b_2.\, \ife{b_1}{b_2}{\false} \\
\min &= \lambda x, y.\, \ife{x < y}{x}{y} \\
\max &= \lambda x, y.\, \ife{x < y}{y}{x} \\
\operatorname{intersect} &= \lambda i_1, i_2.\,\\
&\phantom{::= \lambda}
  \lete{l}{\max \, (\pi_1\, i_1) \, (\pi_1\, i_2)}{\\
  &\phantom{::= \lambda}
  \lete{h}{\min \, (\pi_2\, i_1) \, (\pi_2\, i_2)}{\\
  &\phantom{::= \lambda}
  (l, h)}}
\end{aligned}
$$

### Semantics

The semantics answers precisely what it means to run some expression $e$. We need such a definition to be able to ground any verification that $e$ meets some specification; the correctness theorem will need to talk about what $e$ does (when run) in order to say whether that behavior is correct or not.

We will give a small-step operational semantics for this language; you can look to a programming language theory class to get a broader perspective on other approaches to semantics of a programming language.

The semantics is based is based on a step relation (to be defined below in the [Reduction rules](./hoare.md#reduction-rules) subsection) $e_1 \to e_2$, which intuitively means $e_1$ executes to $e_2$ in one step. We will then generally talk about $e_1 \to^* e_2$, the reflexive and transitive closure of $\to$ (basically, zero or more $\to$ steps between $e_1$ and $e_2$).

$$
e \to^* e \text{ always} \\
e \to^* e'' \text{ if } e \to e' \text{ and } e' \to^* e''
$$

When $e_1 \to^* e_2$, we often say $e_1$ _reduces to_ $e_2$. Reduction is computation in the $\lambda$-calculus. If you were to run a term, it would mean reducing it as much as possible.

If we have $e_1 \to^* v$ (that is, if $e_1$ can reduce to a value specifically), then this is considered a terminating execution. The step relation is defined so that $v \not\to e'$; that is, for any value, it will never step to anything (values are _irreducible_). If we have $e$ and $\forall e', e \not\to e'$ (that is, $e$ is not a value and cannot step to anything), we will say $e$ is "stuck", which is how the semantics encodes $e$ "going wrong" - for example, $1 + \true$ is stuck.

:::: info Exercise

Let $\omega = \fun{x} x \, x$ and $\Omega = \omega \, \omega$. What does $\Omega$ reduce to?

::: details Solution

$\Omega = \omega \, \omega = (\fun{x} x \, x) \, \omega \to (x \, x)[\omega / x] = \omega \, \omega = \Omega$

$\Omega$ reduces to itself! Hence we have a _non-terminating_ expression, also called _diverging_. Note that $\Omega$ is not a value and is not stuck.

Eventually we'll add recursion to the language and then we'll have much more ordinary examples of non-termination.

:::

::::

#### Reduction rules {#reduction-rules}

Rules defining $e_1 \to e_2$ (step relation):

$$
\begin{aligned}
(\lambda x.\, e) v &\to e[v / x] \eqnlabel{(beta reduction)} \\
\ife{\mathrm{true}}{e_1}{e_2} &\to e_1 \\
\ife{\mathrm{false}}{e_1}{e_2} &\to e_2 \\
\pi_1 (v_1, v_2) &\to v_1 \\
\pi_2 (v_1, v_2) &\to v_2 \\
\overline{n_1} + \overline{n_2} &\to \overline{n_1 + n_2} \\
\end{aligned}
$$

$$
\dfrac{n_1 = n_2}{\overline{n_1} == \overline{n_2} \to \true}
\quad
\dfrac{n_1 \neq n_2}{\overline{n_1} == \overline{n_2} \to \false}
$$

$$
\dfrac{n_1 < n_2}{\overline{n_1} < \overline{n_2} \to \true}
\quad
\dfrac{n_1 \geq n_2}{\overline{n_1} < \overline{n_2} \to \false}
$$

The first rule, $(\lambda x.\, e)\, v \to e[v / x]$, is called a _beta reduction_. It's important enough to get special attention, and the name is worth remembering. The notation for _substitution_ $e[v / x]$ means to substitute in $e$ the expression $v$ for each occurrence of the variable $x$. The way to remember the order here (which is [rather standard](https://youtu.be/7HKbjYqqPPQ?t=1925)) is to think of it as $v$ "sits over" $x$. We will not give a formal definition of substitution.

::: warning Capture-avoiding substitution

For the curious, substitution is not entirely straightforward.

There is a generally tricky issue of _variable capture_ when defining substitution. The issue is that if we have an expression like $\lambda y.\, \lambda x.\, x + y$ and try to apply it to the free variable $x$, a naive definition of substitution will reduce to $(\lambda x.\, x + y)[x / y] = \lambda x.\ x + x$. Notice that what was a free variable is now a reference to the lambda abstraction's bound variable; we call this "variable capture" and it's generally considered a bug in substitution. Instead, _capture-avoiding substitution_ will rename bound variables and produce $(\lambda x.\, x + y)[x / y] = \lambda z.\ z + x$, preserving the meaning of the original expression.

The Coq formalism we will eventually use based on Iris does not solve this problem (using a slightly wrong definition of substitution), but we will always substitute closed terms $v$ and in that situation variable capture is not possible.

:::


#### Evaluation contexts

Next, we need to give so-called _structural rules_. The attentive reader will notice that there is no rule for something like $(\lambda x.\, x + 2) (3 + 4)$ - strictly speaking, $3 + 4$ is not a value and the rule for applications does not apply. We'll now fix that.

Here, we'll define structural rules all at once using a technique of _evaluation contexts_. The idea is that in $(\lambda x.\, x + 2) (3 + 4)$, we want to say that the "next operation" is to run $3 + 4$, and when that finishes and produces 7, steps can continue with $(\lambda x.\, x + 2)\, 7$. First, we define an evaluation context:

$$
\begin{aligned}
\text{Evaluation context}\quad K &::= \bullet \mid K\, v \mid e\, K \\
&\phantom{::=} \mid \ife{K}{e_1}{e_2} \\
&\phantom{::=} \mid K + v \mid e + K \\
&\phantom{::=} \mid K < v \mid e < K \\
&\phantom{::=} \mid (K, v) \mid (e, K) \mid \pi_1 \, K \mid \pi_2 \, K
\end{aligned}
$$

An evaluation context is an expression with a hole in it (where the $\bullet$ is). Define $K[e']$ to mean "fill in" the hole with the expression $e'$, producing an expression. For example, $\bullet[e'] ::= e'$ and $(K \, v)[e'] ::= K[e'] \, v$.

::: details Full definition of K[e']

$$
\begin{aligned}
\bullet[e'] &::= e' \\
(K \, v)[e'] &::= K[e'] \, v \\
(e \, K)[e'] &::= e \, K[e'] \\
\left(\ife{K}{e_1}{e_2}\right)[e'] &::= \ife{K[e]}{e_1}{e_2} \\
(K + v)[e'] &::= K[e'] + v \\
(e + K)[e'] &::= e + K[e'] \\
(K < v)[e'] &::= K[e'] < v \\
(e < K)[e'] &::= e < K[e'] \\
(K, v)[e'] &::= \left( K[e'], \, v \right) \\
(e, K)[e'] &::= \left( e, \, K[e'] \right) \\
(\pi_1 \, K)[e'] &::= \pi_1 \, K[e'] \\
(\pi_2 \, K)[e'] &::= \pi_2 \, K[e'] \\
\end{aligned}
$$

:::

Now we add one more rule to define the step relation:

$$
\dfrac{e \to e'}{K[e] \to K[e']} \eqnlabel{step-context}
$$

**Stop and think:** in $e = (\lambda x, y.\, x + y) \, a \, b$ where $a$ and $b$ are expressions and not values, what order are $a$ and $b$ evaluated in? Try to answer this based only on the rules.

::: details Solution

First, let's expand this to $e = ((\lambda x.\, \lambda y.\, x + y) \, a) \, b$. We need to decompose this into something of the form $e = K_0[e']$ for some $K_0$. The only rule for forming evaluation contexts is the one written $e \, K$, which we instantiate to get $K_0 = ((\lambda x.\, \lambda y.\, x + y) \, a) \, \bullet$; $b$ is at the position of the "hole" $\bullet$ and that's what runs first.

This means under this semantics a function with multiple arguments (via currying) has its arguments evaluated _right-to-left_.

:::

**Exercise:** what would you change so that addition $e_1 + e_2$ is evaluated left-to-right? What would you change so tuples $(e_1, e_2)$ could be evaluated in either order?

#### Intuition behind the semantics

The semantics likely mostly follows your intuition, but it makes some things precise. The most obvious element of precision is the evaluation order.

When we have $e = (2 + 3) + (1 + 1)$, the semantics agrees with your intuition that $e \to^* 7$. But what is the actual sequence of $\to$ steps? The rules above give an answer hidden in the evaluation contexts.

The two relevant contexts are $K + v$ and $e + K$. The first does not apply here, since the right-hand side of the sum is not a value yet. Since $1 + 1
\to 2$, $e \to (2 + 3) + 2$. Only then can we use the context $\bullet + 2$ and evaluate in that "hole" position.

Similarly, the beta rule requires that the argument be a value before we perform substitution (this is called a "call-by-value" semantics). Look at how the contexts $K\, v$ and $e\, K$ further tell us that the argument is reduced to a value before reducing the function to a lambda expression.

This semantics is deterministic (you could prove this). A different definition of evaluation contexts could make it non-deterministic, and yet another definition would be deterministic but with everything evaluated left-to-right.

#### Structural evaluation rules

The following _lemmas_ about the step relation can be derived from the step-context rule; they formalize the intuition above that comes from inspecting the semantics.

$$\dfrac{e_2 \to e_2'}{e_1 \, e_2 \to e_1 \, e_2'}$$

$$\dfrac{e_1 \to e_1'}{e_1 \, v_2 \to e_1' \, v_2}$$

$$\dfrac{e_2 \to e_2'}{e_1 + e_2 \to e_1 + e_2'}$$

$$\dfrac{e_1 \to e_1'}{e_1 + v_2 \to e_1' + v_2}$$

## Hoare logic

Hoare logic is based on the _Hoare triples_ $\hoare{P}{e}{\fun{v} Q(v)}$. The intuitive reading of this statement is that "if $P$ holds initially and $e$ terminates in a value $v$, then $Q(v)$ holds". The proposition $P$ is called the pre-condition and $Q$ is the post-condition. The rules of Hoare logic explain how to prove a triple by breaking it down into simpler verification tasks, based on the structure of $e$. Working bottom-up instead, if we prove a Hoare triple about a helper function $\operatorname{bar}$, this can be used in the proof of a larger function $\operatorname{foo}$ at the point where it calls $\operatorname{bar}$, without having to repeat the reasoning about $\operatorname{bar}$.

### Propositions

The Hoare triple has "propositions" $P$ and $Q$. You can proceed to the next sub-section with an intuition that a proposition is a Coq proposition, but eventually (when we upgrade to separation logic) it will be more like a _predicate over the program state_. The main thing to note is that in the Hoare logic rules we use a statement $P \entails Q$ (pronounced "$P$ entails $Q$"), which says "whenever $P$ is true, $Q$ is true".

Let's start with the following grammar for propositions:

$$
\gdef\lift#1{\lceil #1 \rceil}
\mathrm{Propositions}\quad P ::= \lift{\phi} \mid \exists x.\, P(x) \mid \forall x.\, Q(x) \mid P \land Q \mid P \lor Q
$$

where $\phi$ is a "meta-level" proposition (think of it as a Coq proposition, which is what it will be when we use formalization of all of this theory). We will use $\lift{\phi}$ to "lift" a meta-level proposition to the Hoare logic level; in the rest of these notes this conversion will be implicit, to keep things concise.

For now, a Hoare logic proposition $P$ appears no better than Coq propositions. This will change when we move to separation logic.

The rules for proving entailments between propositions are mostly intuitive, and we will come back to them and be more precise with separation logic. However, to give you a flavor here are a few rules:

$$
\dfrac{\lift{\phi}}{P \entails \lift{\phi}}
$$

$$
P \land Q \entails P \quad
P \land Q \entails Q \quad
\dfrac{P \entails Q \quad P \entails R}{P \entails Q \land R}
$$

$$
\dfrac{\forall x.\, (P \entails Q(x))}{P \entails \forall x.\, Q(x)} \eqnlabel{all-intro}
$$

$$
\dfrac{\forall x.\, (P(x) \entails Q)}{\exists x.\, P(x) \entails Q} \eqnlabel{exists-elim}
$$

### Hoare Rules {#hoare-rules}

::: important Reading these rules

It's important to have some fluency with these rules, understanding them intuitively. This first means knowing how to read one of them.

First, remember that above the line is a rule's premises (if there are any) and below is its conclusion.

To read a rule read it **counter-clockwise starting at the bottom left**, starting with the precondition in the goal, then working through the premises and establishing some postcondition, and finally concluding with the postcondition in the goal. At least do this for the consequence and pure-step rules.

:::

$$\hoare{P(v)}{v}{\fun{w} P(w)} \eqnlabel{value}$$

$$
\dfrac{e_1 \to e_2 \quad \hoare{P}{e_2}{\fun{v} Q(v)}}{%
\hoare{P}{e_1}{\fun{v} Q(v)}} \eqnlabel{pure-step}
$$

$$
\dfrac{P' \entails P \quad (\forall v.\, Q(v) \entails Q'(v)) \quad \hoare{P}{e}{Q(v)}}{%
\hoare{P'}{e}{\fun{v} Q'(v)}
}\eqnlabel{consequence}
$$

$$
\dfrac{\hoare{P}{e}{Q} \quad \forall v,\, \hoare{Q(v)}{K[v]}{\fun{w} R(w)}}{%
\hoare{P}{K[e]}{\fun{w} R(w)}} \eqnlabel{bind}
$$

$$
\dfrac{P \entails \lift{\phi} \quad \phi \Rightarrow \hoare{P}{e}{\fun{v} Q(v)}}%
{\hoare{P}{e}{\fun{v} Q(v)}} \eqnlabel{pure}
$$

$$
\dfrac{\forall x.\, \hoare{P(x)}{e}{\fun{v} Q(v)}}{%
\hoare{\exists x.\, P(x)}{e}{\fun{v} Q(v)}} \eqnlabel{exists}
$$

You can think of $\Rightarrow$ as being Coq implication, as opposed to entailment between propositions.

Let's walk through the pure-step rule. It says to prove a triple about $e_1$ with arbitrary pre- and post-conditions, we can switch to a different proof about $e_2$ with the same pre- and post-conditions, if $e_1 \to e_2$. In practice, imagine you're doing a Coq proof whose goal is $\hoare{P}{e_1}{\fun{v} Q(v)}$. Applying this rule would change your goal to a goal with $e_2$ instead, which is _simpler_ because $e_2$ is the result of one step of computation. This is almost like running `simpl` on a Coq goal, but we've moved forward by one step of computation _in the programming language_ as opposed to steps of Coq's functions.

Many presentations of Hoare logic don't use the pure-step rule but following an _axiomatic style_ give one "structural" rule for each language construct.

### Exercise: derive structural rules

Prove the following rules.

$$
\hoare{True}{\overline{n} + \overline{m}}{\fun{v} \overline{n + m}} \eqnlabel{Add}
$$

$$
\hoare{n \neq m}{\overline{n} == \overline{m}}{\fun{v} v = \false} \eqnlabel{IsNeq}
$$

$$
\dfrac{\hoare{P}{e_2}{\fun{v} Q(v)}}{%
\hoare{P}{\ife{\false}{e_1}{e_2}}{\fun{v} Q(v)}
} \eqnlabel{If-false}
$$

::: details Solution

Add: pure-step + value

IsNeq: pure-step + value

If-false: pure-step. Observe that the `if` construct takes a step even when the branches are expressions; this is necessary for this rule to even be sound.

:::

### Soundness

What does it mean to prove $\hoare{P}{e}{\fun{v} Q(v)}$? We have a bunch of "rules" above, but where do they come from?

The reason Hoare logic is useful and what it means to have a (proven) Hoare triple is that we can give a definition of _soundness_ of a Hoare triple that relates it the semantics of programs, and then all the rules given above can be proven as theorems. The soundness definition requires that we interpret propositions, and you can think of that interpretation as being Coq propositions here.

::: important Hoare triple definition/soundness

$\hoare{P}{e}{\fun{v} Q(v)}$ means if $P$ holds and $e \to^* e'$, then either (a) $\exists e''.\, e' \to e''$ ($e'$ is not stuck), or (b) there exists a value $v'$ such that $e' = v'$ and $Q(v')$ holds.

:::

First, notice that Hoare logic connects back to the operational semantics of the programming language and $e$ in particular: we can precisely say how a Hoare triple relates to $e$'s behavior.

Second, notice that we only learn anything about $Q$ if $e \to^* v'$. This is called _partial correctness_ because it only gives the postcondition for programs when the terminate; there is a variant of Hoare logic with so-called _total correctness triples_ that also prove the program terminates, but proving termination can be quite complicated. Do note that regardless of termination, if $P$ holds initially the program is at least _safe_ in that it never does something "bad" like trying to execute $1 + \true$.

::: info Hoare logic as a logic

We have taken the view that a Hoare triple means the soundness statement above, and the rules are proven under that definition. It is also possible to view Hoare logic _as a logic_ where the rules are purely formal axioms of a proof system, and then soundness is a theorem about that proof system.

See [Programming Language Foundations](https://softwarefoundations.cis.upenn.edu/plf-current/HoareAsLogic.html) for a more detailed presentation of this view (note that there are some significant differences in that presentation of Hoare logic and you will likely need to read earlier chapters). An important consequence of formalizing Hoare logic with axioms is the proof of _completeness_ and not just soundness; informally, the rules of Hoare logic are enough to prove any true Hoare triples, and thus we aren't missing any important rules.

:::

### Example: soundness of exists rule

At a high level, this rule can be proven by unfolding the definition of soundness and following rules of propositional logic.

Our goal is a Hoare triple; expanding the definition of soundness for that triple, we have assumptions $\exists x. \, P(x)$ and $e \to^* e'$. We can eliminate the existential to get a specific $x_0$ such that $P(x_0)$ holds. From the premise of this rule, we know $\hoare{P(x_0)}{e}{\fun{v} Q(v)}$ holds. Unfolding the soundness definition in that assumption, we get an implication with two premises: the first is to prove the precondition $P(x_0)$ (which we already have), and the second is to prove $e \to^* e'$ (which we also have). Thus from that Hoare triple we conclude that either $e'$ is reducible or it's a value $v'$ where $Q(v')$ holds, which exactly matches the goal.

### Exercise: soundness of rule of consequence

Go back to the [Hoare rules](./hoare.md#hoare-rules) and look at the rule of consequence. Prove this rule, interpreting the Hoare triples with the definition above.

## Hoare logic verification examples

Here are some examples of correct specifications.

$$
\begin{aligned}
\operatorname{and} &= \lambda b_1, b_2.\, \ife{b_1}{b_2}{\false} \\
\operatorname{add} &= \lambda x, y.\, x + y \\
\min &= \lambda x, y.\, \ife{x < y}{x}{y} \\
\operatorname{f} &= \fun{x} \operatorname{add} \, (\min \, 0 \, x) \, 1 \\
\operatorname{g} &= \fun{x} \ife{x = 1}{\true}{\\ %
&\phantom{= \fun{x}} (\ife{x = 0}{\false}{2 + \false})}
\end{aligned}
$$

$$
\hoare{\True}%
{\operatorname{and} \, b_1 \, b_2}%
{\fun{v} v = \overline{b_1 \mathbin{\&} b_2}}
$$

$$
\hoare{n + m < 2^{64}}%
{\operatorname{add} \, \overline{n} \, \overline{m}}%
{\fun{v} v = \overline{n + m}}
$$

$$
\hoare{\True}%
{\operatorname{min} \, \overline{n} \, \overline{m}}%
{\fun{v} \exists (p: \mathbb{Z}).\, v = \overline{p} \land p \leq n \land p \leq m }
$$

$$
\hoare{n < 2^{64} - 1}%
{\operatorname{f} \, \overline{n}}
{\fun{v} \exists (p: \mathbb{Z}).\, v = \overline{p} \land 1 \leq p}
$$

$$
\hoare{0 \leq n \leq 1}%
{\operatorname{g} \, \overline{n}}
{\fun{v} \True}
$$

The $\operatorname{and}$ spec is an example of giving a strong specification, $\operatorname{add}$ is an example of under-specification (in this case, it would work just as well without the precondition), $\min$ is an under-specification (we could say something stronger in the postcondition and still prove it), $\operatorname{f}$ is the best we can prove assuming the $\operatorname{add}$ and $\min$ specs, and $\operatorname{g}$ is an example where the precondition is necessary and we under-specify in the postcondition.

Even the $\operatorname{and}$ spec is not the strongest possible - notice that the code does not actually require the second argument to be a boolean, and that it only needs to be safe if the first argument is $\true$.

Example proof:

Let's prove the spec for $\operatorname{f}$ above, assuming the other specs. This proof demonstrates using the rules as well as _compositionality_: notice how we end up using the specifications for $\operatorname{min}$ and $\operatorname{add}$ without having to know anything about else about those functions. To conveniently state these intermediate steps, we'll abbreviate the postcondition above as $Q_f(v)$.

First, unfolding $\operatorname{f}$ we see that we have a function application. Apply the pure-step rule and show a beta reduction (substituting $\overline{n}$ for $x$ in the body of $\operatorname{f}$), so that the goal is now

$$
\hoare{n < 2^{64}-1}%
{\operatorname{add} \, (\min \, 0 \, \overline{n}) \, 1}
{\fun{v} Q_f(v)}
$$

We have a function application. The "next thing to run" is the second argument; luckily it's already a value, so the first argument is next. This can be formally expressed by saying that the current expression we're verifying can be decomposed into an evaluation context $K = (\operatorname{add} \, \bullet) \, 1$ around the argument $\operatorname{min} \, 0 \, \overline{n}$. We want to apply the bind rule and produce two goals. The $P$ and $R$ in the rule are determined by matching up the rule's conclusion with our current goal, but $Q$ is a free choice in the below:

$$\hoare{n < 2^{64}-1}{\min \, 0 \, \overline{n}}{\fun{v} Q(v)}$$

$$\forall v.\, \hoare{Q(v)}{\operatorname{add} \, v \, 1}{\fun{v} Q_f(v)}$$

Observe how the bind rule splits up the proof of a complex expression $e' = K[e]$ into a proof about the next expression $e$ (the min reasoning in our current goals), and then a proof about the code that consumes a value $v$ produced by $e$, $K[v]$ (the add reasoning in our current goals). When applied it allows using any intermediate proposition $Q$ to connect the first and second parts.

In this case, we'll take $Q(v) = \exists (p: \mathbb{Z}).\, v = \overline{p} \land p \leq 0 \land p < 2^{64}$. This was derived from a combination of what we learn from the min spec, what we need for the add spec, and some intuition; later we'll see a way of setting up the proof so that it isn't necessary to cleverly come up with this definition.

Let's see how to prove the first goal, using the existing min spec. Unfortunately neither the precondition nor postcondition exactly match up. To make them align, we'll first apply the pure rule to "remember" that $n < 2^{64}-1$. Notice that $n$ is a meta-level variable (a number) for this goal, and what we know about it is buried in a precondition; applying the pure rule allows us to "extract" that knowledge up to the meta level without changing anything about the Hoare triple to be proven. Next, we'll use the rule of consequence, a general-purpose way to use one spec to prove another for the same code. With the assumption $n < 2^{64}-1$, this now works; it just requires some logical reasoning for both entailments.

For the second goal, this time we don't need the pure rule, only the rule of consequence. However, we do need the fact that $p < 2^{64}$ in order to prove that the precondition in the goal implies the precondition in the proven add spec. This is also an opportunity to use the Hoare exists rule. Other than that this goal also comes down to two entailments to be proven.

This completes the proof! Taking a step back, notice how we basically broken down the proof into two steps, one for each sub-call, and then we proved each step by aligning the spec proven for the function with the context in which it was called. This is great for modular reasoning: we can prove a specification, then use (and reuse) it without thinking about the implementation.

### Exercise: prove the triples

Prove the Hoare triples above. Do the proofs as carefully as you can, annotating the rules you use. This is good practice for understanding the rules, and will also help you appreciate when we switch to Coq and it automates the book-keeping for you.
