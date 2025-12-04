---
category: lecture-note
order: 18
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Resource Algebras

## Learning Outcomes

1. Explain how fractional permissions are implemented.
2. Understand how a resource algebra connects to separation logic.

## Motivation

When we saw sequential separation logic, we said `hProp = heap → Prop` where `heap = gmap loc val` (a partial map from locations to values). This allowed us to give a _definition_ of $\ell \mapsto v$ (points-to) and $P \sep Q$ (separating conjunction). Separation in this context meant disjoint memory addresses.

However, we also saw fractional permissions with $\ell \mapsto_{1/2} v$ (a "half" and thus read-only points-to) and $\ell \mapsto_{\box} v$ (a persistent read-only points-to). These seems unrelated to the definitions above, so how do they connect?

Remember that fractional and persistent permissions are useful, especially with concurrency: remember that when we spawn a thread $e$, we have to split up our permissions into $\wp(e, \True)$ (which the spawned thread gets) and $P$ (which the rest of the code gets). If the only splitting possible were disjoint locations, it would be hard to verify any useful concurrent code: threads would need to be completely independent.

In this lecture we'll generalize separation logic by changing the definition of `hProp` and what it means to split. However, we won't throw everything away: all the separation logic rules will remain exactly the same. In this lecture we'll be focused on the _assertions_ of separation logic; nothing will change about _program_ proofs.

## Model of separation logic

In order to generalize separation logic, it helps to lay out some terminology for what we're doing.

The _logic_ consists of the syntax (things like $P \sep Q$ and $P \wand Q$) and rules (like $P \sep (Q \sep R) \entails (P \sep Q) \sep R$ and $P \sep (P \wand Q) \entails Q$). This part won't change.

We can use a logic abstractly, following the rules to prove $P \entails Q$ for various propositions.

A _model_ of the logic is an interpretation or definition for the propositions and syntax where the rules can be proven as theorems. We introduced separation logic alongside a model where propositions are predicates over heaps, and separating conjunction $(P \sep Q)(h)$ holds when $P$ and $Q$ hold over disjoint subsets $h_1$ and $h_2$ of $h$.

Notice that I said **a** model and not **the** model. The same logic can have more than one model! That's exactly what we'll do today.

An example you might be familiar with comes from geometry. Euclid's axioms include a parallel postulate: if you have a line and a point not on the line, there is exactly one line parallel to the given line which goes through the given point. If you remove that axiom, then there are multiple possible models of Euclid's axioms: Euclidean geometry, hyperbolic geometry, and elliptic geometry.

## Algebraic model of separation logic

Let's try to sketch out the ingredients of this generalization. Instead of ownership over one location and one value specifically, we'll want ownership to be more flexible. Wanting to stay as general as possible, let's say we'll pick a type $A$ and own elements $x : A$, which we'll refer to as _resources_. An $\iProp$ will represent a set of resources $A \to \Prop$; it's a set because separation logic propositions can describe one of several possible worlds, just like before an hProp could be true in zero or several heaps.

We need a way to represent ownership of one specific resource: we'll write it $\own(x) : \iProp$ for the resource $x : A$. The heap model was a special case: the resources were heaplets, and we had special syntax $\ell \mapsto v : \operatorname{hProp}$ for the resource that represents ownership over a single location and its value. Now we'd write that as $\own(\{\ell \mapsto v\})$.

One of the things we need for separation logic is to split and combine resources, to implement the _separation_ in the name of the logic. Combining is easier: the assertion $\own(x) \sep \own(y)$ should hold for some resource which combines the two sides separately. We have some arbitrary type $A$, but now we'll assume we can combine two resources in $A$, which we'll write $x \cdot y$ ("x compose y"). Splitting will essentially be the reverse, where we have $\own(x \cdot y) \entails \own(x) \sep \own(y)$.

There's still one thing missing, which is the idea if disjointness in $P \sep Q$. The way we'll incorporate this is a bit indirectly: we'll define $\valid x$ ("valid x") to say that some elements are valid, and others are not. $\own(x)$ will only be true for a resource $y$ if $x = y$ _and_ $\valid x$. The assertion $\own(x) \sep \own(y)$ is equivalent to $\own(x \cdot y)$, which means that it implies $\valid(x \cdot y)$, and $h_1 \cdot h_2$ when the heaps overlap will be defined to produce something invalid, thus $P \sep Q$ with only points-to assertions will retain its previous meaning that $P$ and $Q$ hold over disjoint parts of the heap.

What we've described is the beginning of a _resource algebra_ $A$: it defines some resources, a way to split and combine them, and a subset of valid ones to define when we're allowed to combine them.

::: info Aside on algebra

We're about to define more formally what a resource algebra is using an _algebraic structure_ There are many algebraic structures (such as fields, monoids, groups, and vector spaces). If you've never seen this setup (say, from an abstract algebra class), the setup for a resource algebra might seem strange to you.

It might help to see the rules for a different structure, a monoid, which are simpler than RAs.

A monoid is a structure $(M, +)$ with a carrier type $M$ (of elements "in the monoid") and a single operation $(+) : M \to M \to M$ that adds or "composes" two elements. The addition operation must be associative; that is $\forall x, y, z.\; (x + y) + z = x + (y + z)$.

Our first example of a monoid is the integers. The carrier is $\mathbb{Z}$ and addition is the usual addition operation.

Our second example is the monoid of lists with elements of type $A$ (this needs to be fixed but the specifics don't matter), where $+$ is list concatenation. Notice that this operation is associative but not commutative, which is fine.

Notice that there are three levels here: a monoid is the collection of all types with these properties, then we have a _specific type_ like list which is a monoid, and then we have a _specific element_ like `[2; 5; 3]` of the list monoid.

:::

### Resource algebra definition

A resource algebra (RA) is a collection of "resources" that can be combined and split. It will help to keep in mind two concrete examples we've already seen. The first is our core example of heaps, which can be split and combined into disjoint subsets and was our original model of separation logic. The other is a slightly odd example of how we combine and split fractions $q$, which we saw when we split and combined $\ell \mapsto_{q} v$ for some fixed location $\ell$ and value $v$. That example is odd in that the resource algebra will only manipulate the fraction and we won't worry about multiple locations yet.

Formally, a resource algebra (RA) is an algebraic structure $(A, \cdot, \valid)$. It has these components:

| component | type            | description                         |
| :-------- | :-------------- | :---------------------------------- |
| $A$       | Type            | carrier; an $x : A$ is a "resource" |
| $(\cdot)$ | $A \to A \to A$ | resource composition                |
| $\valid$  | $A \to \bool$   | valid resources                     |

- $A$ is a type called the carrier of the resource algebra. In our examples this is a heap and a $q$ fraction respectively. For the heap RA we'll need to add an "error" value $\errorval$ for invalid compositions.
- $(\cdot) : A \to A \to A$ combines two resources. The expression $x \cdot y$ can be pronounced "x compose y" (or "x plus y"). For the heap RA, $h_1 \cdot h_2$ is disjoint union. In that case, we will have $h_1 \cdot h_2 = \errorval$ if $h_1$ and $h_2$ overlap.
- $\valid : A \to \bool$ says which elements are valid. We pronounced $\valid(x)$ as "valid x". For the heap RA, all resources are valid except $\errorval$. For fractions, $\valid(q) \triangleq 0 < q \leq 1$.

Let's walk through each example:

**Heap resource algebra:** The resources of the heap resource algebra are heaplets, subsets of the heap, or an error value $\bot$. Two heaps can be combined if they are disjoint; otherwise they produce the error value. Any heaplet is valid (but not $\bot$).

**Fractional resource algebra:** The resources of the fractional resource are fractions $q$. Any two fractions can be combined by addition, but only fractions $0 < q \leq 1$ are valid. No fraction has a core.

### RAs in the logic

Resource algebras are defined this way so that for a given RA with carrier $A$, we can use $A \to \Prop$ as the model of a separation logic proposition, a type I'll call iProp (though the Iris model, the actualy definition of iProp, is much more complicated to address a number of other concerns). The core ownership proposition is $\own(x)$, which asserts ownership of a single resource $x : A$.

Two key properties ownership will satisfy:

$\own(x) \entails \lift{\valid{x}}$

$\own(x \cdot y) \bient \own(x) \sep \own(y)$

In this model, we can interpret the various parts of separation logic. Note that for each of these definitions we give them as a function, just like the definitions with hProp were all functions of the heap.

$\own(x)(y) \triangleq x = y \land \valid x$

$(P \sep Q)(x) \triangleq \exists (x_1: A), (x_2: A).\, x = x_1 \cdot x_2 \land P(x_1) \land P(x_2)$

The definition of separating conjunction gives us $\own(x) \sep \own(y) \entails \own(x \cdot y)$, but the reverse doesn't follow from these definitions directly; it will actually require some additional properties about $\valid$ and $(\cdot)$.

**Exercise:** confirm that the definition of $\ell_1 \mapsto v_1 \sep \ell_2 \mapsto v_2$ with $\ell \mapsto v$ defined as $\own(\{\ell \mapsto v\})$ matches the definition you would expect from our original heap model of separation logic assertions prior to this lecture. What happens if $\ell_1 = \ell_2$ under the two definitions?

**Exercise:** prove $\ell_1 \mapsto v_1 \sep \ell_2 \mapsto v_2 \entails \lift{\ell_1 \neq \ell_2}$.

For the above rules to make sense, we actually can't have just any RA with the signatures above. There is a bit more to a valid resource algebra, namely some _laws_ (properties) that the $(A, (\cdot), \valid)$ components need to satisfy. Here are the laws:

- $\forall x, y.\; x \cdot y = y \cdot x$ (commutativity)
- $\forall x, y, z.\; x \cdot (y \cdot z) = (x \cdot y) \cdot z$ (associativity)
- $\forall x, y.\; \valid(x \cdot y) \to \valid(x)$ (valid-op)

These rules are needed so that ownership follows all the separation logic rules we had earlier; without them, we would have contradictions in the logic which would render the whole thing useless. For example, we need $\own(x) \sep \own(y)$ to be the same as $\own(y) \sep \own(x)$ (separating conjunction is commutative); since these two are equivalent to $\own(x \cdot y)$ and $\own(y \cdot x)$ respectively using our earlier rule about ownership splitting, we actually need $x \cdot y = y \cdot x$ or we run into problems (specifically, the logic becomes unsound).

The last rule might look oddly asymmetric. The reason we only need this one rule is that $\valid(x \cdot y) = \valid(y \cdot x)$ (due to commutativity of composition), and thus we can prove from the above that $\valid(x \cdot y) \to \valid(x) \land \valid(y)$. This rule is what proves $\own(x \cdot y) \entails \own(x) \sep \own(y)$; ownership of the two resources together implies validity of $x \cdot y$, and this is enough to guarantee validity of the subresources.

## An RA for fractional permissions

We can now build up the specific RA used to implement $\ell \mapsto_q v$. We'll do this in two stages: we'll first define an RA for a one-location heap with fractions, then we'll extend it to multiple locations (this part is mostly straightforward).

### Fractions for one location

We'll define $\operatorname{fracRA}(V)$; this is an RA parameterized by an arbitrary type of values $V$. Making it general is intended to help you understand the definition - no part of this definition will care what specific values are used, although eventually they'll be the $\val$ of our programming language.

The carrier type will be $\mathbb{Q} \times V \union \{\bot\}$; that is, the elements of this RA will be of the form $(q, v)$ (a fraction $q : \mathbb{Q}$ and a value $v : V$), or a special error value $\errorval$ used for invalid compositions.

The resource composition operation will be defined as:

- $(q_1, v) \cdot (q_2, v) = (q_1 + q_2, v)$ (notice these are the same value)
- $(q_1, v_1) \cdot (q_2, v_2) = \errorval$ if $v_1 \neq v_2$
- just for completeness, $\bot \cdot x = x \cdot \bot = \bot$, as you might expect

Validity is defined as $\valid((q, v)) \triangleq 0 < q \leq 1$, and $\errorval$ is not valid.

The partial core is never defined.

Notice how fractions are divided and combined as before, and we make explicit in this definition that combining requires that the values are the same.

### The full fractional heap RA

We'll now define a $\operatorname{heapRA}(L, V)$ parameterized by a type of addresses or locations $L$ and values $V$. Again, the specific types won't matter for the definition, and we'll use $\Loc$ and $\val$ for our actual programming language.

The carrier is a partial map from $L$ to the carrier of $\operatorname{fracRA}(V)$. It's common to refer to an algebraic structure like $\operatorname{fracRA}(V)$ directly but actually means its carrier (a type); remember technically the RA is a tuple with the carrier and the composition and validity functions.

We'll see that the behavior of this RA mostly defers to how $\operatorname{fracRA}(V)$ works, which is why we defined that RA first.

The composition $h_1 \cdot h_2$ will be defined pointwise: take the union of the two maps, and if $h_1(l) = x$ and $h_2(l) = y$, the composed heap will have the value $x \cdot y$ using the composition of the fracRA resource algebra.

A heap is valid $\valid(h)$ if all of its values are valid, according to the validity of fracRA.

The "primitive" resources in this RA have the shape $\{\ell \mapsto (q, v)\}$: single-location heaplets, with values that are tuples of a fraction and a value. These heaplets are exactly those that we will abbreviate $\ell \mapsto_q v \triangleq \own(\{\ell \mapsto (q, v)\})$.

**Exercise:** confirm that this makes sense; that is, this definition of $\ell \mapsto_q v$ splits and combines the way you expect for fractions given the general rules for $\own$.

## Persistence

We omitted discussion of persistence above. With the definitions above, we can already have resources that can be duplicated: if in an RA we had a resource that satisfied $x = x \cdot x$, then $\own(x) \entails \own(x) \sep \own(x)$. The persistent points-to is defined using an RA that extends fractions to have exactly such an element. Let's first see that construction, which we call _discardable fractions_, before talking about persistence.

### Discardable fractions

The carrier is a type with three possibilities: a fraction, a marker that the fraction has been discarded, or a combination of both. We'll write the three possibilities DfracOwn($q$), DfracDiscarded, and DfracBoth($q$). You can get a good intuition for this RA by thinking of DfracDiscarded as an extremely small fraction $\epsilon$ and DfracBoth($q$) as $1 + q$.

Here are some examples of composition. You can predict the rules with the intuition above, formally treating $\epsilon + \epsilon = \epsilon$.

- $\text{DfracOwn}(q_1) \cdot \text{DfracOwn}(q_2) = \text{DfracOwn}(q_1 + q_2)$
- $\text{DfracOwn}(q) \cdot \text{DfracDiscarded} = \text{DfracBoth}(q)$
- $\text{DfracDiscarded} \cdot \text{DfracDiscarded} = \text{DfracDiscarded}$
- $\text{DfracBoth}(q_1) \cdot \text{DfracBoth}(q_2) = \text{DfracBoth}(q_1 + q_2)$

The valid elements are the following:

- $\valid \text{DfracOwn}(q) = 0 < q \leq 1$
- $\valid \text{DfracDiscarded} = \True$
- $\valid \text{DfracBoth}(q) = 0 < q < 1$

The purpose of discardable fractions is to have an element $\text{DfracDiscarded}$ which is duplicable: $\own(\text{DfracDiscarded}) \entails \own(\text{DfracDiscarded}) \sep \own(\text{DfracDiscarded})$. However, we haven't actually explained how to obtain such an element; that will be the subject of the next lecture on ghost state.

### Partial core

Iris has a definition of a `Persistent P` where `P: iProp`, and `l ↦[uint64T]□ #x` is an example of such a persistence proposition. However, `Persistent P` is _not_ defined as `P ⊢ P ∗ P`; it has a slightly stronger definition which gives persistence some additional properties (we won't get into them here in detail). A key feature of the Iris definition is that it also allows defining the persistently modality, which is used to define Hoare triples and implement the Iris Proof Mode's persistent context.

The way persistence is defined requires adding another operation $\pcore$ (partial core) to the RA structure that every RA must also implement, in addition to composition and validity.

If you want the full details on the partial core, its laws, examples of its definition, and how it is used to implement the persistently modality, and you're generally interested in how Iris is implemented rather than how to use it, you should read [Iris from the ground up](https://people.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf).

Here is a very short description, only to pique your interest: For an RA with carrier type $A$, $\pcore$ has the type $A \to \option(A)$. The intuition behind the partial core is that if $\pcore(x) = \Some(y)$, then $y$ is the "shareable", persistent part of $x$; the operation is partial so that $\pcore(x) = \None$ means there is _no_ shareable component of $x$. A key law for partial cores is that if $\pcore(x) = \Some(y)$, then $x \cdot y = x$. Notice the special case of $\pcore(x) = \Some(x)$; in this case $x = x \cdot x$ and $\own(x) \entails \own(x) \sep \own(x)$. We can now _define_ the persistently modality in terms of a resource algebra model: $(\box P)(r) \triangleq \exists r'. \pcore(r) = \Some(r') \land P(r')$.
