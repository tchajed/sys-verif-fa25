---
category: lecture
order: 6
shortTitle: "Lecture 6+7: Hoare Logic"
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Lectures 6 and 7: Hoare Logic

## Learning outcomes

1. Understand how a small-step operational semantics explains what a program does.
2. Explain what a Hoare triple means.
3. Use Hoare logic rules to prove (simple) programs on paper.

---

<!-- @include: ./macros.snippet.md -->

## Introduction

We have so far taken a view of program verification where the code is a functional program in Coq, the specification is a property about that function, and the proof uses any Coq-level reasoning required; we specifically developed a style where the code is an ADT and the specification relates it to a model.

We will now develop Hoare logic, a formal system for reasoning about program correctness. At first, the code will still be functional programs. The specifications will use a new style of pre- and post-conditions, attached to each function. Proofs will use the rules of Hoare logic to handle each programming feature and to compose existing specifications together. Hoare logic will provide a smooth path to separation logic and concurrent separation logic, which add extensions for reasoning about more interesting programs while retaining much of the basic structure of this simple version.

::: important Reading these notes

These lecture notes are written in a bottom-up style: each definition is presented in detail, then used later. This is intended to be a good reference but you will not need to understand every detail before moving on.

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

At a high level, the language is built around _expressions_ and _values_. Values are simpler: they are the data of the language, in this case consisting of first-class functions, numbers, booleans, and tuples. Expressions are where the computation lives, and include arithmetic, comparison between numbers, and a conditional `if` expression. What especially typifies expressions is that they _evaluate to values_, as opposed to being run to have side effects like _statements_ in other languages. Hence why we see no construct in this language like `x := v` to assign a (mutable) variable. `if` is a bit special in that we have it as an expression (which evaluates to either the `then` side or the `else` side), unlike the `if` statement in C or Java, for example.

<!--
\gdef is like \def but defines a command in the global KaTeX context, for
subsequent math blocks.
-->

$$
\begin{aligned}
&\mathrm{Expressions} &e &::= x \mid v \mid \fun{x} e \mid \app{e_1}{e_2} \\
&&&\phantom{::=} \mid \ife{e}{e_1}{e_2} \\
&&&\phantom{::=} \mid e_1 + e_2 \mid e_1 == e_2 \mid e_1 < e_2 \\
&&&\phantom{::=} \mid (e_1, e_2) \mid \pi_1 \, e \mid \pi_2 \, e \\
&\mathrm{Values} &v &::= \lambda x.\, e \mid \overline{n} \mid \mathrm{true} \mid \mathrm{false} \mid (v_1, v_2)
\end{aligned}
$$

Common syntactic sugar:

$$
\begin{aligned}
\fun{x, y} e &::= \fun{x} \fun{y} e \\
\lete{x}{e_1} e_2 &::= (\fun{x} e_2) \, e_1 \\
e_1 \, e_2 \, e_3 &::= (\app{e_1}{e_2}) \, e_3
\end{aligned}
$$

Some notation is worth explaining here. The notation uses _metavariables_ to indicate what is being defined; $e$ always refers to an expression, $v$ to a value, $x$ to a variable, and $n$ to a number. When we write $v ::= \true \mid \false$, this defines variables $v$ to be either the constant $\true$ or $\false$ (the vertical bar separates alternatives, just like a Coq `Inductive`). The grammar for expressions includes one alternative $e ::= v$, which says that any value (defined above) can also be used as an expression. The grammar defines a recursive inductive datatype for expressions and for values; the definitions refer to each other ($e ::= v$ refers to values when defining expressions, but also $v ::= \fun{x} e$ says anonymous functions are values and the body is an expression), so we have _mutually recursive inductives_.

The grammar rule $e ::= x$ says that a variable like $x$ or $y$ is an expression ($e$ in the grammar). $v ::= \overline{n}$ says that an integer constant $\overline{n}$ is a value; the overline is used to distinguish between a meta-level number $n : \mathbb{Z}$ and the literal $\overline{n}$ which is a value in the language. $\pi_1 \, e$ and $\pi_2 \, e$ are "projection functions" (often denoted using $\pi$) that get the first and second element of a tuple, respectively.

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
  \lete{l}{\max \, (\pi_1\, i_1) \, (\pi_1\, i_2)}\\
  &\phantom{::= \lambda}
  \lete{h}{\min \, (\pi_2\, i_1) \, (\pi_2\, i_2)}\\
  &\phantom{::= \lambda}
  (l, h)
\end{aligned}
$$

### Semantics

The semantics answers precisely what it means to run some expression $e$. We need such a definition to be able to ground any verification that $e$ meets some specification; the correctness theorem will need to talk about what $e$ does (when run) in order to say whether that behavior is correct or not.

We will give what is called a _small-step operational semantics_ for this language; you can look to a programming language theory class to get a broader perspective on other approaches to semantics of a programming language.

The semantics is based on a step relation (to be defined below in the [Reduction rules](./hoare.md#reduction-rules) subsection) $e_1 \to e_2$. This is just a relation that we use special notation for; it's not implication. Intuitively, $e_1 \to e_2$ is defined in such a way that it means $e_1$ executes to $e_2$ in one execution step. We will then generally talk about $e_1 \to^* e_2$, which allows zero or more $\to$ steps between $e_1$ and $e_2$; formally it would be defined by these rules:

$$
e \to^* e \text{ always} \\
e \to^* e'' \text{ if } e \to e' \text{ and } e' \to^* e''
$$

When $e_1 \to^* e_2$, we often say $e_1$ _reduces to_ $e_2$. **Reduction is computation** in the $\lambda$-calculus. If you wrote an interpreter for this language, it would mean reducing it as much as possible. If we have $e_1 \to^* v$ (that is, if $e_1$ can reduce to a value specifically), then this is considered a terminating execution. The step relation is defined so that $v \not\to e'$; that is, for any value, it will never step to anything (values are _irreducible_). If we have $e$ and $\forall e', e \not\to e'$ (that is, $e$ is not a value and cannot step to anything), we will say $e$ is "stuck", which is how the semantics encodes $e$ "going wrong" - for example, $1 + \true$ is stuck.

:::: info Exercise

Let $\omega = \fun{x} x \, x$ and $\Omega = \omega \, \omega$. What does $\Omega$ reduce to?

::: details Solution

$\Omega = \omega \, \omega = (\fun{x} x \, x) \, \omega \to (x \, x)[\omega / x] = \omega \, \omega = \Omega$

$\Omega$ reduces to itself! Hence we have a _non-terminating_ expression, also called _diverging_. Note that $\Omega$ is not a value and is not stuck.

Eventually we'll add recursion to the language and then we'll have much more ordinary examples of non-termination.

:::

::::

There are three things an expression can do: it can reduce to a value, it can reduce to a _stuck_ expression, and it might have an infinite chain of reductions (it also might do more than one of these if the relation $e_1 \to e_2$ is non-deterministic!). A good interpreter would throw some sort of exception or print an error message if an expression gets stuck (for example, `1 + true` is such an example) but we haven't written a semantics for _what_ error messages should be printed. This is a language designed for verification so we won't be too worried about exactly how programs go wrong; we're in the business of proving _correct_ programs.

#### Reduction rules {#reduction-rules}

Rules defining $e_1 \to e_2$ (step relation):

$$
\begin{aligned}
(\lambda x.\, e) v &\to e[v / x] \eqnlabel{(beta reduction)} \\
\ife{\mathrm{true}}{e_1}{e_2} &\to e_1 \eqnlabel{(if-true)} \\
\ife{\mathrm{false}}{e_1}{e_2} &\to e_2 \eqnlabel{(if-false)} \\
\pi_1 \, (v_1, v_2) &\to v_1 \eqnlabel{(proj-fst)} \\
\pi_2 \, (v_1, v_2) &\to v_2 \eqnlabel{(proj-snd)} \\
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

Hoare logic is based on the _Hoare triples_ $\hoare{P}{e}{\fun{v} Q(v)}$. The intuitive reading of this statement is that "if $P$ holds initially and $e$ terminates in a value $v$, then $Q(v)$ holds". The proposition $P$ is called the pre-condition and $Q$ is the post-condition. Note that $Q$ is a _function of a value_, which is the value that $e$ reduces to (if it loops forever and doesn't reduce to a value, the Hoare triple doesn't say anything). To give a reminder that the postcondition is a function, these notes will write $\lambda v,\, Q(v)$. On the board we will also write $\hoare{P}{e}{v.\, Q(v)}$ to give a name $v$ to the return value, omitting the $\lambda$ to save some space.

The rules of Hoare logic explain how to prove a triple by breaking it down into simpler verification tasks, based on the structure of $e$. Working bottom-up instead, if we prove a Hoare triple about a helper function $\operatorname{bar}$, this can be used in the proof of a larger function $\operatorname{foo}$ at the point where it calls $\operatorname{bar}$, without having to repeat the reasoning about $\operatorname{bar}$.

### Propositions {#propositions}

The Hoare triple has "propositions" $P$ and $Q$. You can proceed to the next sub-section with an intuition that a proposition is a Coq proposition, but eventually (when we upgrade to separation logic) it will be more like a _predicate over the program state_. The main thing to note is that in the Hoare logic rules we use a statement $P \entails Q$ (pronounced "$P$ entails $Q$"), which says "whenever $P$ is true, $Q$ is true".

Let's start with the following grammar for propositions:

$$
\mathrm{Propositions}\quad P ::= \lift{\phi} \mid \exists x.\, P(x) \mid \forall x.\, Q(x) \mid P \land Q \mid P \lor Q
$$

where $\phi$ is a "meta-level" proposition (think of it as a Coq proposition, which is what it will be when we use formalization of all of this theory). We will use $\lift{\phi}$ to "lift" a meta-level proposition to the Hoare logic level; in the rest of these notes this conversion will be implicit, to keep things concise.

For now, a Hoare logic proposition $P$ appears no better than Coq propositions. This will change when we move to separation logic.

The rules for proving entailments between propositions are mostly intuitive, and we will come back to them and be more precise with separation logic. However, to give you a flavor here are a few rules:

$$
\dfrac{\lift{\phi}}{P \entails \lift{\phi}} \eqnlabel{prop-pure} \quad
\dfrac{P \entails \phi \quad \phi \Rightarrow (P \entails Q)}{P \entails Q} \eqnlabel{prop-from-pure}
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

### Proof rules {#hoare-rules}

::: important Reading these rules

It's important to have some fluency with these rules. This first means knowing how to read them.

First, remember that above the line is a rule's premises (if there are any) and below is its conclusion.

In general with such proof rules, you will want to start by looking for _axioms_, or rules without premises. These are the ends of a proof, where using these rules will finish the proof. For other rules (which will be the majority) you will want to read rules from the conclusion to the premises: the effect of `apply`ing in Coq is to transform a goal that looks like the conclusion into the premises. If there's a Hoare triple in both, then the one in the premise is the "rest of the proof" and the rest of the premises are "side conditions" required to apply this rule.

For Hoare logic more specifically, read rules **counter-clockwise starting at the bottom left**, starting with the precondition in the goal, observe what preconditions are provided in the premises, see what postcondition needs to be established, and finally see what postcondition this concludes in by looking at the goal. Try doing this to understand what the consequence and pure-step rules accomplish.

:::

It's best for the purpose of this class to think about $\hoare{P}{e}{\fun{v} Q(v)}$ as a Coq `Prop` that says $e$ has a particular specification, with a definition that we haven't yet given. The rules below are then theorems proven with that definition. There are two consequences to this view:

- The specifications we write will quantify over Coq-level variables (implicitly in the notes, but in Coq we will have to be explicit about this). For example, $\hoare{\True}{\operatorname{add}  \, \overline{n} \, \overline{m}}{\fun{v} v = \overline{n + m}}$ should be viewed as being for all values of the Coq variables $n : \mathbb{Z}$ and $m : \mathbb{Z}$.
- In addition to using the rules of Hoare logic, we can also use Coq reasoning principles, like `destruct` and arithmetic reasoning about $n$ and $m$. The rules will handle anything specific to programs.

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
\dfrac{\hoare{P}{e}{\fun{v} Q} \quad \forall v,\, \hoare{Q(v)}{K[v]}{\fun{w} R(w)}}{%
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

### Example: consequences of bind rule

The bind rule is likely to be one of the most confusing, especially because it makes use of evaluation contexts. To illustrate what it does, here are some rules derived from it using examples of how evaluation contexts are constructed.

::: important Learning by doing

The following examples are something you could construct yourself while reading a text like this, to generate your own exercise: take the bind rule and the rules for evaluation constructs, plug in some possible contexts for $K$, and see what the result rules say. Many things you learn (e.g., papers you read, the Intel Architectures Developer's Manual, the entire memcached codebase) will not be "scaffolded" appropriately like this, and being able to construct your own exercises to build understanding is an extremely valuable skill.

:::

Remember that $\lete{x}{e_1} e_2$ is just $(\fun{x} e_2) \, e_1$.

$$
\dfrac{
\hoare{P}{e_1}{\fun{v} Q(v)} \quad
\forall v.\, \hoare{Q(v)}{e_2[v / x]}{R}
}{%
\hoare{P}{\lete{x}{e_1} e_2}{R}
} \eqnlabel{hoare-let}
$$

We know that first the expression $e_1$ is evaluated, then the result is substituted into $e_2$ and that is evaluated. Observe that the hoare-let rule says we can prove a let expression in a mirrored way with two steps: show $e_1$ takes $P$ to an intermediate condition $Q$, then that $e_2$ takes $Q(v)$ to $R$. The proof for $e_2$ has to be carried out for any $v$ subject only to $Q(v)$ since we don't know in that proof what $e_1$ will return other than what the specification says.

This rule is derived by choosing $K = (\fun{x} e_2) \, \bullet$. What is not so obvious is that we didn't determine exactly _where_ inside $e_1$ the next step will occur; that step might be buried further within the expression. However, the Hoare bind rule doesn't care about this and still lets us split the proof this way.

Another derived rule, for `if` expressions:

$$
\dfrac{
\begin{array}{c}
\hoare{P}{e}{\fun{c} (c = \true \land Q_t) \lor (c = \false \land Q_f)} \\
\hoare{Q_t}{e_1}{R} \quad
\hoare{Q_f}{e_2}{R} \quad
\end{array}
}{
\hoare{P}{\ife{e}{e_1}{e_2}}{R}
} \eqnlabel{hoare-if}
$$

This chooses a particular specification for the intermediate condition, but a very general one: we need $e$ to produce a boolean since `if` only works on booleans, and other than that this rule allows one proof where $e$ returns true and has postcondition $Q_t$ and another for false with postcondition $Q_f$. The `if` subsequently becomes one of the branches, and the premises require a proof about each branch.

### Exercise: derive structural rules for pure steps

Many presentations of Hoare logic don't use the pure-step rule but following an _axiomatic style_ give one "structural" rule for each language construct.

Prove the following structural rules.

$$
\hoare{True}{\overline{n} + \overline{m}}{\fun{v} \overline{n + m}} \eqnlabel{hoare-add}
$$

$$
\hoare{n \neq m}{\overline{n} == \overline{m}}{\fun{v} v = \false} \eqnlabel{hoare-neq}
$$

$$
\dfrac{\hoare{P}{e_2}{Q}}{%
\hoare{P}{\ife{\false}{e_1}{e_2}}{Q}
} \eqnlabel{hoare-if-false}
$$

::: details Solution

hoare-add: pure-step + value

hoare-neq: pure-step + value

hoare-if-false: pure-step. Observe that the `if` construct takes a step even when the branches are expressions; this is necessary for this rule to even be sound.

:::

## Hoare logic verification examples

Here are some examples of correct specifications.

$$
\gdef\and{\operatorname{and}}
\gdef\add{\operatorname{add}}
\begin{aligned}
\and &= \lambda b_1, b_2.\, \ife{b_1}{b_2}{\false} \\
\add &= \lambda x, y.\, x + y \\
\min &= \lambda x, y.\, \ife{x < y}{x}{y} \\
\operatorname{f} &= \fun{x} \add \, (\min \, 0 \, x) \, 1 \\
\operatorname{g} &= \fun{x} \ife{x = 1}{\true}{\\ %
&\phantom{= \fun{x}} (\ife{x = 0}{\false}{\overline{2} + \false})} \\
\operatorname{h} &= \fun{x} \ife{\and \, (0 < x) \, (x < 0)}{\overline{1} + \true}{\overline{2}} \\
\end{aligned}
$$

$$
\hoare{\True}%
{\and \, b_1 \, b_2}%
{\fun{v} v = \overline{b_1 \mathbin{\&} b_2}}
$$

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

$$
\hoare{n < 2^{64} - 1}%
{\operatorname{f} \, \overline{n}}
{\fun{v} \exists (p: \mathbb{Z}).\, v = \overline{p} \land p \leq 1}
$$

$$
\hoare{0 \leq n \leq 1}%
{\operatorname{g} \, \overline{n}}
{\fun{v} \True}
$$

$$
\hoare{\True}%
{\operatorname{h} \, \overline{n}}
{\fun{v} v = \overline{2}}
$$

The $\operatorname{and}$ spec is an example of giving a strong specification, $\operatorname{add}$ is an example of under-specification (in this case, it would work just as well without the precondition), $\min$ is an under-specification (we could say something stronger in the postcondition and still prove it), $\operatorname{f}$ is the best we can prove assuming the $\operatorname{add}$ and $\min$ specs, and $\operatorname{g}$ is an example where the precondition is necessary and we under-specify in the postcondition.

Even the $\operatorname{and}$ spec is not the strongest possible - notice that the code does not actually require the second argument to be a boolean, and that it only needs to be safe if the first argument is $\true$.

### Example proof: specification for f

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

You may want to start by reading the next section on Hoare outlines and writing an outline-based proof sketch, and only then trying to do a detailed proof.

## Hoare outlines

Writing an on-paper proof referencing these rules is quite tedious and obscures some important aspects of the proofs. There's another commonly used format for expressing a proof in Hoare logic that captures the essence of the reasoning: the _Hoare outline_. To use the outline, we will need programs to be primarily written with let-bindings; this names all the subexpressions and makes obvious what order computations happen in, as opposed to it coming from the language semantics and implicit in the program. Observe how in $\lete{x}{f \, 1} \lete{y}{g \, 2} x + y$ it's clear that $f$ runs first and then $g$, while $(f \, 1) + (g \, 2)$ is ambiguous from just the syntax, and in fact evaluates $g \, 2$ first based on the language semantics above.

Here's a specification for a function written in this style, with let bindings. The specification is written vertically to fit a big program; it means exactly the same thing as the horizontal version.

$$
\hoareV{n < 2^{64} - 1}%
{\begin{aligned}
\letV{m}{\min \, 0 \, \overline{n}} \\
\letV{y}{\operatorname{add} \, m \, 1} \\
&y
\end{aligned}
}%
{\exists (p: \mathbb{Z}.\, y = p \land p \leq 1)}
$$

And here is a Hoare outline for the above specification, which you can think of as a "proof sketch" for the Hoare triple but not all the individual details.

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

The Hoare outline gives a statement true at that point in the code, starting with the precondition and ending at the postcondition. We re-use the program variables as variables in the outline's propositions. Whenever a line has $\lete{x}{f \, x \, y} \dots$, we'll apply a specification for $f$. For the Hoare outline to be a valid proof, the condition above should imply $f$'s precondition, and the line below should be the postcondition (in both cases we may need to instantiate the specification's variables appropriately). We can also write two statements in a row if the first implies the second, which helps adapt pre- and post-conditions. Note how these rules about what makes a Hoare outline work are implicitly justified by the rule of consequence (do you see why?).

In this language all variables are immutable and there's no state other than the variables (the language is purely functional), so any line of the outline as statements that remain true forever afterward; this will no longer be true once the program has mutable state.

::: important Hoare logic supports modular proofs

Something that you probably take for granted if you have even just a little programming experience is that if you're working on a big function `f`, you'll split into some helper functions `h1` and `h2` that `f` then calls. This is a more modular implementation. Ideally (if the split is a good one) when you're working on `f` you don't have to think about the complete code of `h1` and `h2`, because you just have some abstract "specification" in mind of what they do.

Hoare logic supports _modular reasoning_ that exactly reflects this split into helper functions: we prove a specification about `h1` and `h2`, then prove `f` by referring to those specifications without needing to know how they're implemented. Modularity is important to scale up a proof to a big piece of code, and in this case it's elegant that the way the proof is modular (by writing specifications for functions) matches how the code is modular.

Modularity is also beneficial when a helper function is reused, since then the proof of `h1` can be done just once and used multiple times. However, it has benefits even if a function is used only once since it breaks down a big task into smaller, more manageable tasks. In a larger team modularity even permits you to split and parallelize the work: if you can decide what `h1` does (its _specification_), then one person can implement `h1` and another can use it in `f` at the same time.

:::

## Soundness {#soundness}

What does it mean to prove $\hoare{P}{e}{\fun{v} Q(v)}$? We have a bunch of "rules" above, but where do they come from?

The reason Hoare logic is useful and what it means to have a (proven) Hoare triple is that we can give a definition of _soundness_ of a Hoare triple that relates it to the semantics of programs, and then all the rules given above can be proven as theorems. The soundness definition requires that we interpret propositions, and you can think of that interpretation as being Coq propositions here.

::: important Hoare triple definition/soundness

$\hoare{P}{e}{\fun{v} Q(v)}$ means if $P$ holds and $e \to^* e'$, then either (a) $\exists e''.\, e' \to e''$ ($e'$ is not stuck), or (b) there exists a value $v'$ such that $e' = v'$ and $Q(v')$ holds.

:::

First, notice that Hoare logic connects back to the operational semantics of the programming language and $e$ in particular: we can precisely say how a Hoare triple relates to $e$'s behavior.

Second, notice that we only learn anything about $Q$ if $e \to^* v'$. This is called _partial correctness_ because it only gives the postcondition for programs when the terminate; there is a variant of Hoare logic with so-called _total correctness triples_ that also prove the program terminates, but proving termination can be quite complicated. Do note that regardless of termination, if $P$ holds initially the program is at least _safe_ in that it never does something "bad" like trying to execute $1 + \true$.

::: info Hoare logic as a logic

We have taken the view that a Hoare triple means the soundness statement above, and the rules are proven under that definition. It is also possible to view Hoare logic _as a logic_ where the rules are purely formal axioms of a proof system, and then soundness is a theorem about that proof system.

See [Programming Language Foundations](https://softwarefoundations.cis.upenn.edu/plf-current/HoareAsLogic.html) for a more detailed presentation of this view (note that there are some significant differences in that presentation of Hoare logic and you will likely need to read earlier chapters). An important consequence of formalizing Hoare logic with axioms is the proof of _completeness_ and not just soundness; informally, the rules of Hoare logic are enough to prove any true Hoare triples, and thus we aren't missing any important rules.

:::

### Example: soundness of exists rule {#ex-soundness-exists}

At a high level, this rule can be proven by unfolding the definition of soundness and following rules of propositional logic.

Our goal is a Hoare triple; expanding the definition of soundness for that triple, we have assumptions $\exists x. \, P(x)$ and $e \to^* e'$. We can eliminate the existential to get a specific $x_0$ such that $P(x_0)$ holds. From the premise of this rule, we know $\hoare{P(x_0)}{e}{\fun{v} Q(v)}$ holds. Unfolding the soundness definition in that assumption, we get an implication with two premises: the first is to prove the precondition $P(x_0)$ (which we already have), and the second is to prove $e \to^* e'$ (which we also have). Thus from that Hoare triple we conclude that either $e'$ is reducible or it's a value $v'$ where $Q(v')$ holds, which exactly matches the goal.

### Exercise: soundness of rule of consequence {#ex-soundness-consequence}

Go back to the [proof rules](./hoare.md#hoare-rules) and look at the rule of consequence. Prove this rule, interpreting the Hoare triples with the definition above.
