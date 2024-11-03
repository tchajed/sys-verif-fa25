---
category: lecture
order: 18
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Lecture 18: Resource Algebras

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

We'll actually give a very general model of separation logic where heaps are replaced with "resources". I'll start calling the propositions `iProp` so that `hProp` is reserved for the definition with heaps specifically; this is much closer to how Iris actually works, hence `iProp`. Abstractly, `iProp` will be a $\operatorname{Res} \to Prop$ where we'll write some rules for what $\operatorname{Res}$ should look like (they will form a _resource algebra_). Then concretely we'll pick a particular $\operatorname{Res}$ that gives fractional and persistent permissions. The reason to do this in these two steps is that we'll see other examples of resource algebras, and having the generality in place will help you unify the various definitions.

::: info Aside on algebra

There are many algebraic structures (such as fields, monoids, groups, and vector spaces). If you've never seen an algebraic structure, this setup might seem strange to you. The definition of a monoid is simpler to get across, but an RA has more operations and rules than a monoid:

A monoid is a structure $(M, +)$ with a carrier type $M$ (of elements "in the monoid") and a single operation $(+) : M \to M \to M$ that adds or "composes" two elements. The addition operation must be associative; that is $\forall x, y, z.\; (x + y) + z = x + (y + z)$.

Our first example of a monoid is the integers. The carrier is $\mathbb{Z}$ and addition is the usual addition operation.

Our second example is the monoid of lists with elements of type $A$ (this needs to be fixed but the specifics don't matter), where $+$ is list concatenation. Notice that this operation is associative but not commutative, which is fine.

:::

### Resource algebra definition

A resource algebra (RA) is a collection of "resources" that can be combined and split. It will help to keep in mind two concrete examples we've already seen: heaps, which can be split and combined into disjoint subsets; and for a fixed $\ell$ and $v$ $\ell \mapsto_q v$ can be viewed as a collection of resources (one for each fraction $q$) that is split and combined by addition (we'll get to multiple locations and values later).

More formally, an RA is an algebraic structure $(A, \cdot, \valid, \pcore)$. Here's a quick reference of what the components are:

| component | type               | description                         |
| :-------- | :----------------- | :---------------------------------- |
| $A$       | Type               | carrier; an $x : A$ is a "resource" |
| $(\cdot)$ | $A \to A \to A$    | resource composition                |
| $\valid$  | $A \to \bool$      | valid resources                     |
| $\pcore$  | $A \to \option(A)$ | partial core                        |

To understand why this is how a resource algebra is defined, it will help to see how it will be "plugged into" a separation logic assertion later. After we pick some resource algebra for our separation logic, we'll add $\own(x)$ as a separation logic proposition where $x : A$ to represent ownership of the resource $x$. Now we won't need a special syntax for $\ell \mapsto v$; it will be _defined_ to be $\own(\{h \mapsto v\})$ (that is, ownership over the singleton heap).

- $A$ is a type called the carrier of the resource algebra. In our examples this is a heap and a $q$ fraction respectively. For the heap RA we'll need to add an "error" value $\errorval$.
- $(\cdot) : A \to A \to A$ combines two resources. The expression $x \cdot y$ can be pronounced "x dot y" (you might also hear "plus"). For the heap RA, $h_1 \cdot h_2$ is disjoint union. In that case, we will have $h_1 \cdot h_2 = \errorval$ if $h_1$ and $h_2$ overlap.
- $\valid : A \to \bool$ says which elements are valid. We pronounced $\valid(x)$ as "valid x". For the heap RA, all resources are valid except $\errorval$. For fractions, $\valid(q) \triangleq 0 < q \leq 1$.
- $\pcore : A \to \option(A)$ is the "partial core" of a resource. When $\pcore(x) = \Some(p)$, it says that the "shareable" part of $x$ is $p$. The operation is partial, so $\pcore(y) = \None$ says there is no persistent/shareable part of $y$. This is the most unusual part of the RA definition.

Let's walk through each example:

**Heap resource algebra:** The resources of the heap resource algebra are heaplets, subsets of the heap, or an error value $\bot$. Two heaps can be combined if they are disjoint; otherwise they produce the error value. Any heaplet is valid (but not $\bot$). No heaplet has a core. Observe that the singleton heaps $\{\ell \mapsto v\}$ function as the "smallest" resources.

**Fractional resource algebra:** The resources of the fractional resource are fractions $q$. Any two fractions can be combined by addition, but only fractions $0 < q \leq 1$ are valid. No fraction has a core.

### RAs in the logic

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
