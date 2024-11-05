---
category: lecture
order: 18
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Lecture 18: Resource Algebras

::: warning Draft

This lecture is still a draft.

:::

## Learning Outcomes

1. Explain how fractional permissions are implemented.

## Motivation

When we saw sequential separation logic, we said `hProp = heap → Prop` where `heap = gmap loc val` (a partial map from locations to values). This allowed us to give a _definition_ of $\ell \mapsto v$ (points-to) and $P \sep Q$ (separating conjunction). Separation in this context meant disjoint memory addresses.

However, we also saw fractional permissions with $\ell \mapsto_{1/2} v$ (a "half" and thus read-only points-to) and $\ell \mapsto_{\box} v$ (a persistent read-only points-to). These seems unrelated to the definitions above.

We do want fractional and persistent permissions. With concurrency, remember that when we spawn a thread $e$, we have to split up our permissions into $\wp(e, \True)$ (which the spawned thread gets) and $P$ (which the rest of the code gets). If the only splitting possible were disjoint locations, it would be hard to write any useful code: threads would need to be completely independent.

In this lecture we'll generalize separation logic by changing the definition of `hProp` and splitting. However, we won't throw everything away: all the separation logic rules will remain exactly the same. In this lecture we'll be focused on the _assertions_ of separation logic; nothing will change about _program_ proofs.

## Model of separation logic

In order to generalize separation logic, it helps to lay out some terminology for what we're doing.

The _logic_ consists of the syntax (things like $P \sep Q$ and $P \wand Q$) and rules (like $P \sep (Q \sep R) \entails (P \sep Q) \sep R$ and $P \sep (P \wand Q) \entails Q$). This part won't change.

We can use a logic abstractly, following the rules to prove $P \entails Q$ for various propositions.

A _model_ of the logic is an interpretation or definition for the propositions and syntax where the rules can be proven as theorems. We introduced separation logic alongside a model where propositions are predicates over heaps, and separating conjunction $(P \sep Q)(h)$ holds when $P$ and $Q$ hold over disjoint subsets $h_1$ and $h_2$ of $h$.

Notice that I said **a** model and not **the** model. The same logic can have more than one model! That's exactly what we'll do today.

As an example, you might be familiar with comes from geometry. Euclid's axioms include a parallel postulate: if you have a line and a point not on the line, there is exactly one line parallel to the given line which goes through the given point. If you remove that axiom, then there are multiple possible models of Euclid's axioms: Euclidean geometry, hyperbolic geometry, and elliptic geometry.

## Algebraic model of separation logic

Let's try to sketch out the ingredients of this generalization. Instead of ownership over one location and one value specifically, we'll want ownership to be more flexible. Wanting to stay as general as possible, let's say we'll pick a type $A$ and own elements $x : A$, which we'll refer to as resources. An $\iProp$ will represent a set of resources $A \to \Prop$; it's a set because separation logic propositions can describe one of several possible worlds, just like before an hProp could be true in zero or several heaps.

We need a way to represent ownership of one specific resource: we'll write it $\own(x) : \iProp$ for the resource $x : A$. The heap model was a special case: the resources were heaplets, and we had special syntax $\ell \mapsto v : \operatorname{hProp}$. Now we'd write that as $\own(\{\ell \mapsto v\})$.

One of the things we need for separation logic is to split and combine resources, to implement the _separation_ in the name of the logic. Combining is easier: the assertion $\own(x) \sep \own(y)$ should hold for some resource which combines the two sides. We have some arbitrary type $A$, but now we'll assume we can combine two resources in $A$, which we'll write $x \cdot y$ ("x compose y"). Splitting will essentially be the reverse, where we have $\own(x \cdot y) \entails \own(x) \sep \own(y)$.

There's still one thing missing, which is that for heaps at least disjointness was somehow relevant to $P \sep Q$. The way we'll incorporate this is a bit indirectly: we'll define $\valid x$ ("valid x") to say that some elements are valid, and others are not. $\own(x)$ will only be true for a resource $y$ if $x = y$ _and_ $\valid x$. We'll make sure $\own(x) \sep \own(y)$ will only be provable when $\valid(x \cdot y)$, and overlapping heaps do not combine to something valid.

What we've described is the beginning of a _resource algebra_ $A$: it defines some resources, a way to split and combine them, and a subset of valid ones to define when we're allowed to combine them.

::: info Aside on algebra

We're about to define more formally what a resource algebra is.

There are many algebraic structures (such as fields, monoids, groups, and vector spaces). If you've never seen an algebraic structure, the setup for a resource algebra might seem strange to you. The definition of a monoid is simpler to get across, but an RA has more operations and rules than a monoid:

A monoid is a structure $(M, +)$ with a carrier type $M$ (of elements "in the monoid") and a single operation $(+) : M \to M \to M$ that adds or "composes" two elements. The addition operation must be associative; that is $\forall x, y, z.\; (x + y) + z = x + (y + z)$.

Our first example of a monoid is the integers. The carrier is $\mathbb{Z}$ and addition is the usual addition operation.

Our second example is the monoid of lists with elements of type $A$ (this needs to be fixed but the specifics don't matter), where $+$ is list concatenation. Notice that this operation is associative but not commutative, which is fine.

:::

### Resource algebra definition

A resource algebra (RA) is a collection of "resources" that can be combined and split. It will help to keep in mind two concrete examples we've already seen. The first is our core example of heaps, which can be split and combined into disjoint subsets and was our original model of separation logic. The other is a slightly odd example of how we combine and split fractions $q$, which we saw when we split and combined $\ell \mapsto_{q} v$ for some fixed location $\ell$ and value $v$. That example is odd in that the resource algebra will only manipulate the fraction and we won't worry about multiple locations yet.

Formally, a resource algebra (RA) is an algebraic structure $(A, \cdot, \valid, \pcore)$. It has these components:

| component | type               | description                         |
| :-------- | :----------------- | :---------------------------------- |
| $A$       | Type               | carrier; an $x : A$ is a "resource" |
| $(\cdot)$ | $A \to A \to A$    | resource composition                |
| $\valid$  | $A \to \bool$      | valid resources                     |
| $\pcore$  | $A \to \option(A)$ | partial core                        |

- $A$ is a type called the carrier of the resource algebra. In our examples this is a heap and a $q$ fraction respectively. For the heap RA we'll need to add an "error" value $\errorval$ for invalid compositions.
- $(\cdot) : A \to A \to A$ combines two resources. The expression $x \cdot y$ can be pronounced "x dot y" (you might also hear "plus"). For the heap RA, $h_1 \cdot h_2$ is disjoint union. In that case, we will have $h_1 \cdot h_2 = \errorval$ if $h_1$ and $h_2$ overlap.
- $\valid : A \to \bool$ says which elements are valid. We pronounced $\valid(x)$ as "valid x". For the heap RA, all resources are valid except $\errorval$. For fractions, $\valid(q) \triangleq 0 < q \leq 1$.
- $\pcore : A \to \option(A)$ is the "partial core" of a resource. When $\pcore(x) = \Some(p)$, it says that the "shareable" part of $x$ is $p$. The operation is partial, so $\pcore(y) = \None$ says there is no persistent/shareable part of $y$. This is the most unusual part of the RA definition. A special case that is particularly important is that if $\pcore(y) = \Some(y)$, then $y$ is entirely shareable, which will correspond exactly to persistence later in separation logic.

Let's walk through each example:

**Heap resource algebra:** The resources of the heap resource algebra are heaplets, subsets of the heap, or an error value $\bot$. Two heaps can be combined if they are disjoint; otherwise they produce the error value. Any heaplet is valid (but not $\bot$). We can define $\pcore(h) = \Some(\empty)$. Observe that the singleton heaps $\{\ell \mapsto v\}$ function as the "smallest" useful resources.

**Fractional resource algebra:** The resources of the fractional resource are fractions $q$. Any two fractions can be combined by addition, but only fractions $0 < q \leq 1$ are valid. No fraction has a core.

### Discardable fractions

Let's see a brand new example, which will demonstrate pcore. This example is like the RA for fractions, extending them to support persistence.

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

This RA has a non-trivial partial core:

- $\pcore(\text{DfracOwn}(q)) = \None$
- $\pcore(\text{DfracDiscarded}) = \text{DfracDiscarded}$
- $\pcore(\text{DfracBoth}(q)) = \text{DfracDiscarded}$

Notice that DfracDiscarded is its own core, which is what makes it persistent.

### RAs in the logic

To understand why this is how a resource algebra is defined, it will help to see how it will be "plugged into" a separation logic assertion later. After we pick some resource algebra for our separation logic, we'll add $\own(x)$ as a separation logic proposition where $x : A$ to represent ownership of the resource $x$. Now we won't need a special syntax for $\ell \mapsto v$; it will be _defined_ to be $\own(\{h \mapsto v\})$ (that is, ownership over the singleton heap).

We introduced $\own(x)$ to represent ownership of $x$ in the logic. We will also organize things so that $\own(x)$ will always imply $\valid(x)$; owning invalid resources is forbidden. What can we do with resources? A key rule is $\own(x \cdot y) \bient \own(x) \cdot \own(y)$. That is, if we have $\own(z)$ and it can be _split_ into $z = x \cdot y$, then we can also split it into two _separate_ ownership assertions. Furthermore we can also work backwards and combine ownership.

**Exercise:** confirm that $\own(\{\ell_1 \mapsto v_1\} \cdot \{\ell_2 \mapsto v_2\})$ splits the way you expect given $\ell \mapsto v$ is defined to be $\own(\{\ell \mapsto v\})$ and the earlier definition of $P \sep Q$. What happens if $\ell_1 = \ell_2$ in this example?

For the above rules to make sense, we actually can't have just any RA with the signatures above. There is a bit more to a valid resource algebra, namely some _laws_ (properties) that the $(A, (\cdot), \valid, \pcore)$ components need to satisfy. Here are the laws, except for the $\pcore$ laws which we'll skip for now:

- $\forall x, y.\; x \cdot y = y \cdot x$
- $\forall x, y, z.\; x \cdot (y \cdot z) = (x \cdot y) \cdot z$
- $\forall x, y.\; \valid(x \cdot y) \to \valid(x)$

These rules are needed so that ownership behaves sensibly in the logic, given the separation logic rules we want to be true. For example, we need $\own(x) \sep \own(y)$ to be the same as $\own(y) \sep \own(x)$ (separating conjunction is commutative); since these two are equivalent to $\own(x \cdot y)$ and $\own(y \cdot x)$ respectively using our earlier rule about ownership splitting, we actually need $x \cdot y = y \cdot x$ or we run into problems (specifically, the logic becomes unsound).

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

Notice how fractions are divided and combined as before, but combining requires that the values are the same.

### The full fractional heap RA

We'll now define a $\operatorname{heapRA}(L, V)$ parameterized by a type of addresses or locations $L$ and values $V$. Again, the specific types won't matter for the definition, and we'll use $\Loc$ and $\val$ for our actual programming language.

The carrier is going to be a partial map from $L$ to $\operatorname{fracRA}(V)$. Technically the type of values is the _carrier type of that RA_, but it's common in abstract algebra to make a pun between these.

We'll see that the behavior of this RA mostly defers to how $\operatorname{fracRA}(V)$ works, which is why we defined that first.

The composition $h_1 \cdot h_2$ will be defined pointwise: take the union of the two maps, and if $h_1(l) = x$ and $h_2(l) = y$, the composed heap will have the value $x \cdot y$ using the composition of the fracRA resource algebra.

A heap is valid $\valid(h)$ if all of its values are valid, according to the validity of fracRA.

We'll define the partial core $\pcore(h)$ to be a heap of the partial cores of the locations in $h$, excluding those locations that have no core. Observe how we define this in terms of the fracRA partial core, even though we haven't defined any partial cores; this allows us to use this definition later when we replace fracRA with something that _does_ have partial cores.
