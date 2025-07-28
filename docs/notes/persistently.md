---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture
tags: literate
order: 15
shortTitle: "Lecture 15: Persistently"
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Lecture 15: The persistently modality

> Follow these notes in Coq at [src/sys_verif/program_proof/persistently.v](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/src/sys_verif/program_proof/persistently.v).

## Learning outcomes

- Appreciate the value of having persistent propositions.
- Explain the difference between a Hoare triple as a Prop and as an iProp.

## Motivation

We know that separation logic propositions are generally not duplicable ($P \nvdash P \sep P$). This is because we interpret propositions as asserting exclusive ownership, for example over heap locations. However, ownership does not _have_ to be exclusive. We've already seen one example with pure propositions $\lift{\phi}$, which can be freely duplicated and in the IPM even moved out of the spatial context into the Coq context. Another example where ownership isn't exlusive is if a pointer is _read-only_, it is safe to have many copies of its points-to fact, as long as those assertions are used only for reading and not writing.

Before getting into modalities, let's revisit the mechanisms in Coq for read-only pointers.

```rocq
From sys_verif.program_proof Require Import prelude empty_ffi.
From New.proof Require Import std.
From sys_verif.generatedproof.sys_verif_code Require Import memoize.

Section proof.
Context `{hG: !heapGS Σ} `{!goGlobalsGS Σ}.

#[global]
Program Instance : IsPkgInit memoize := ltac2:(build_pkg_init ()).

```

## Read-only pointers

We saw in a previous lecture, and in the [fractions guide](/notes/program-proofs/fractions.md), how _fractional permissions_ can be used for read-only access.

Recall the basic splitting/recombining rule:

$l ↦_{q_1 + q_2} v ⊣⊢ l ↦_{q_1} v ∗ l ↦_{q_2} v$

We can see splitting at work in this example, which first splits the assertion `l ↦ x` (using `iDestruct`, which knows to split a fractional points-to into two halves), then uses the two halves for the two loads.

Fractions also support _combining_ to recover full ownership and go back to being able to write to the pointer.

```rocq
Lemma split_fraction_example (l: loc) (x: w64) :
  {{{ l ↦ x ∗ ⌜uint.Z x < 100⌝ }}}
    let: "y" := ![#uint64T] #l in
    let: "z" := ![#uint64T] #l in
    #l <-[#uint64T] ("y" + "z")
  {{{ RET #(); l ↦ (word.add x x) }}}.
Proof.
  wp_start as "[Hx %Hbound]".
  iDestruct "Hx" as "[Hx1 Hx2]".
```

:::: info Goal diff

```txt title="goal diff"
  Σ : gFunctors
  hG : heapGS Σ
  goGlobalsGS0 : goGlobalsGS Σ
  l : loc
  x : w64
  Φ : val → iPropI Σ
  Hbound : uint.Z x < 100
  ============================
  "Hx" : l ↦ x // [!code --]
  "Hx1" : l ↦{#1 / 2} x // [!code ++]
  "Hx2" : l ↦{#1 / 2} x // [!code ++]
  "HΦ" : ▷ (l ↦ word.add x x -∗ Φ (# ()))
  --------------------------------------∗
  WP let: "y" := ![# uint64T] (# l) in
     let: "z" := ![# uint64T] (# l) in # l <-[# uint64T] "y" + "z"
  {{ v, Φ v }}
```

::::

```rocq
  wp_auto.
  iCombine "Hx1 Hx2" as "Hx".
```

:::: info Goal diff

```txt title="goal diff"
  Σ : gFunctors
  hG : heapGS Σ
  goGlobalsGS0 : goGlobalsGS Σ
  l : loc
  x : w64
  Φ : val → iPropI Σ
  Hbound : uint.Z x < 100
  ============================
  "Hx1" : l ↦{#1 / 2} x // [!code --]
  "Hx2" : l ↦{#1 / 2} x // [!code --]
  "HΦ" : l ↦ word.add x x -∗ Φ (# ())
  "Hx" : l ↦ x // [!code ++]
  --------------------------------------∗
  WP # l <-[# uint64T] # (word.add x x) {{ v, Φ v }}
```

::::

```rocq
  wp_store.
  wp_auto.
  iApply "HΦ".
  iFrame.
Qed.

```

## Persistent propositions

Fractions are good but don't directly give something duplicable. The _persistent points-to_ will solve this problem.

Persistent propositions are a core feature of Iris. They are important enough that the Iris Proof Mode has a separate _persistent context_; so far it has been empty so we haven't seen it. The persistent context is separate from the _spatial context_. The persistent context contains only persistent resources, which are duplicable, but they are not pure, so they can talk about the heap memory for example. When we split a proof with `iSplitL` or when using `iApply` the persistent context will always be available in all subgoals; the assertions are implicitly duplicated by the proof mode when splitting.

The IPM goals in general look like the following:

```txt title="IPM goal"
P, Q: iProp Σ
------------
"HP": P
----------□
"HQ": Q
----------∗
R
```

As usual, there is a Coq context above everything. The separation logic part has separation logic hypotheses "HP" and "HQ", and separation logic conclusion R. The fact that "HP" is in the persistent context implies that P is persistent - this means $P ⊢ P ∗ P$. (The full definition is more than that, but we won't go deep enough into how Iris works to talk about it.)

So what propositions are persistent? First, the pure propositions are persistent - but they can be put into the Coq context, so they aren't so interesting. The first "real" example we'll see is the persistent points-to, `l ↦□ v`.

```rocq
Lemma alloc_ro_spec (x: w64) :
  {{{ True }}}
    alloc #x
  {{{ (l: loc), RET #l; l ↦□ x }}}.
Proof.
  wp_start as "_".
  rewrite -wp_fupd.
  wp_apply wp_alloc as "%l H".

```

This is the step where we persist the points-to permission and turn it into a persistent, read-only fact. Using `struct_pointsto_persist` requires the `iMod` tactic, which we will cover later when we talk about concurrency; for now think of it as a variation on `iDestruct`.

```rocq
  iPersist "H" as "Hro".
```

:::: info Goal diff

```txt title="goal diff"
  Σ : gFunctors
  hG : heapGS Σ
  goGlobalsGS0 : goGlobalsGS Σ
  x : w64
  Φ : val → iPropI Σ
  l : loc
  ============================
  "Hro" : l ↦□ x // [!code ++]
  --------------------------------------□ // [!code ++]
  "HΦ" : ∀ l0 : loc, l0 ↦□ x -∗ Φ (# l0)
  "H" : l ↦ x // [!code --]
  --------------------------------------∗
  |={⊤}=> Φ (# l)
```

::::

Notice from the goal diff that the output (renamed to "Hro" for clarity) is put into a separate list of hypotheses - this is the persistent context.

To obtain the persistent points-to assertion, we have to give up the regular fractional assertion, and this operation is _not_ reversible - the persistence relies on the location never being written to.

```rocq
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame "Hro".
Qed.

```

With a persistent permission, it's reasonable (and expected) that the permission need not be returned in the postcondition.

```rocq
Lemma read_discarded_spec (l: loc) (x: w64) :
  {{{ l ↦□ x }}}
    ![#uint64T] #l
  {{{ RET #x; True }}}.
Proof.
  wp_start as "#H".
  wp_apply (@wp_load_ty with "[$H]"). iIntros "_".
  iApply "HΦ". auto.
  Unshelve.
Qed.

```

### Exercise: why not return the points-to?

When an assertion is persistent, we don't need to return it in the postcondition. Why?

## The persistently modality

Motivated by this kind of shared ownership, we introduce a modality called the "persistently" modality, written $□P$. When $P$ is a proposition, $□P$ is another proposition which asserts that $P$ holds but without exclusive ownership.

The main fact about persistently is that it is automatically duplicable: $□P ⊢ □P ∗ P$. It is also the case that $□P ∗ P ⊢ □P$. So $□P$ behaves a bit like $\lift{\phi}$ so far - if we prove it, it will remain true and not get "used up" in a proof.

The general idea of a modality in logic is that it is a _shade of truth_ of another proposition. This can be a confusing concept, so we will approach it in several different ways. On first read, you need not understand the rest of this section; it might help to start by seeing it used in proofs in Coq before going back to the theory. We'll also be able to be more precise when we talk about concurrency.

To understand the explanations of persistently it helps to anticipate a little of what we will talk about when introducing ghost state to reason about concurrent programs. Thus far, we said separation logic propositions have been predicates over the heap. We will extend this to be predicates over _resources_, where individual heap locations will be just one example. In fact we've already seen that the fractional permission $\ell ↦_{1/2} v$ can't be explained as a predicate over the heap (what do we do with the $1/2$ part? what does separation mean?). We will have to leave the notion of a "resource" abstract for now, but we will have regular exclusive resources, and persistent resources. $□P$ means $P$ holds over only the persistent resources. For now, you can imagine that we divide the heap into a two parts $(h_r, h_w)$ where $h_r$ is read-only. The read-only part turns out to be duplicable, in that we can consider $h_r$ and $h_r$ to be separate for proving $P ∗ Q$; there's no conflict between them since the values in that part of the heap don't change. On the other hand if $P$ and $Q$ mention exclusive resources (locations in $h_w$), then for $P ∗ Q$ to be true in a heap those read-write locations would have to be disjoint.

First, it is useful to ask whether $□P$ is stronger or weaker than $P$ (in general a modality could be neither, but the modalities in Iris are one or the other). In this case, the answer is that it is _stronger_: $□P ⊢ P$ but not vice versa (in general). Intuitively, it's because $□P$ requires $P$ hold using only "persistent resources".

Second, the persistence modality is monotonic - if $P ⊢ Q$, then $□P ⊢ □Q$. I think in some ways this is a basic sanity test of a modality, but I am not sure about this in general.

Third, since $□P$ is $P$ using only persistent resources, $□P ⊢ □□P$; both sides don't use resources, and saying it twice makes no difference.

### Exercise: introduction rule

Prove this derived rule:

$$
\dfrac{□P ⊢ Q}{□P ⊢ □Q} \eqnlabel{persistently-intro}
$$

Fourth, a core feature of persistence is this rule:

$$
\dfrac{S ⊢ □P ∧ Q}%
{S ⊢ □P ∗ Q} \eqnlabel{persistently-sep}
$$

This is more complicated than the other properties. We won't go into too much detail on this one, since it requires a little more understanding of resources than we have right now.

Finally, we will introduce a notion of a "persistent proposition". Define `Persistent P` to be true if $P ⊢ □P$. For example, $ℓ ↦□ v$ is persistent.

Don't get confused between $P$ being persistent and $□P$ ("persistently $P$")! If $P$ is persistent, observe that adding the modality in front makes no difference - $P ⊣⊢ □P$ from the rules above. On the other hand we can write $□Q$ for any $Q$, whether it's persistent or not.

### Exercise: test your intuition about persistently

What do you think $□(ℓ ↦ v)$ means?

---

## Memoization example

A core use of persistence is in Hoare triples, when they are used _within the logic_; that is, when we need to refer to the specification of a function within a proposition. The natural place this comes up is whenever a function is a value in our code, either as a parameter or as a struct field. We'll now introduce an extended example on memoization to introduce this.

You should start by quickly reading the code for this example at [go/memoize/memoize.go](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/go/memoize/memoize.go).

### MockMemoize proof

As a warmup, we'll verify the "MockMemoize" implementation. This version still has to store and call the function, but there's no memoization happening - when we use `m.Call(x)` it just always calls `f(x)`.

There is another difference between the two implementations: we use a `*MockMemoize` whereas we'll use `Memoize` - one is always used through a pointer, while the other is used as a value. Both would work in this case, we're just illustrating what this looks like in the proofs.

---

To give a specification to the memoization library, we will require that the user prove that the provided function, which we'll call `f_code` (of type `val`, since it's a function in GooseLang), implements a Gallina function `f : w64 → w64`. This is more restrictive than strictly necessary, but we do need it to have some Hoare triple, since it must at minimum be safe to call, and if we want to say anything about the result of `Call` we also need to know what it does. The choice here is to require it to implement some pure function over integers, but which is one is arbitrary.

The core of the proof is the representation invariant for a `*MockMemoize`. The most interesting part of that invariant is how we say that `f_code` implements `f: w64 → w64`.

```rocq
Definition fun_implements (f_code: func.t) (f: w64 → w64) : iProp Σ :=
  ∀ (x:w64), {{{ True }}} #f_code #x {{{ RET #(f x); True }}}.

#[export] Instance fun_implements_persistent f_code f :
  Persistent (fun_implements f_code f).
Proof. apply _. Qed.

```

`fun_implements` is different from what you've seen so far in this class because it states the correctness of `f_code` as an `iProp` rather than a `Prop`. This is significant later, when we'll use `fun_implements` inside a precondition.

The way this works is that a Hoare triple $\hoare{P}{e}{Q}$ when used as an iProp actually expands to:

$$□(P \wand \wp(e, Q))$$

### Exercise: what does persistently of a wand mean?

Try to puzzle out what it means to prove this persistently vs not. You might want to come back to this after seeing the memoization proof (even for the mock memoization library) and where `fun_implements` is used.

---

There are several interesting things in the representation function `own_mock_memoize` below:

- The `□` in `m ↦[MockMemoize :: "f"]□ f_code` makes this a persistent, read-only field points-to fact.
- The names "#Hf" and "#Hf_spec" have a # which means they will be added to the Iris Proof Mode's persistent context when introduced.

```rocq
Definition own_mock_memoize (m: loc) (f: w64 → w64) : iProp Σ :=
   ∃ (f_code: func.t),
     "#Hf" :: m ↦s[memoize.MockMemoize :: "f"]□ f_code ∗
     "#Hf_spec" :: fun_implements f_code f.

Lemma wp_NewMockMemoize (f_code: func.t) (f: w64 → w64) :
  {{{ is_pkg_init memoize ∗ fun_implements f_code f }}}
    memoize @ "NewMockMemoize" #f_code
  {{{ l, RET #l; own_mock_memoize l f }}}.
Proof.
  wp_start as "#Hfun".
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  goGlobalsGS0 : goGlobalsGS Σ
  f_code : func.t
  f : w64 → w64
  Φ : val → iPropI Σ
  ============================
  _ : is_pkg_init memoize
  "Hfun" : fun_implements f_code f
  --------------------------------------□
  "HΦ" : ∀ l : loc, own_mock_memoize l f -∗ Φ (# l)
  --------------------------------------∗
  WP exception_do
       (let: "f" := alloc (# f_code) in
        return: alloc
                  (let: "$f" := ![# funcT] "f" in
                   struct.make (# memoize.MockMemoize)
                     (list.Cons (# "f"%go, "$f") (alist_val []))))
  {{ v, Φ v }}
```

::::

```rocq
  (* NOTE: [wp_apply] will lose the |==> (update) modality here, but we can add
  it ourselves with this rewrite. *)
  rewrite -wp_fupd.
  wp_auto.
  wp_alloc m as "Hm".
  wp_auto.
  iApply struct_fields_split in "Hm". iNamed "Hm".
  iSimpl in "Hf".
  iPersist "Hf".
```

:::: info Goal diff

```txt title="goal diff"
  Σ : gFunctors
  hG : heapGS Σ
  goGlobalsGS0 : goGlobalsGS Σ
  f_code : func.t
  f : w64 → w64
  Φ : val → iPropI Σ
  f_ptr, m : loc
  ============================
  _ : is_pkg_init memoize
  "Hfun" : fun_implements f_code f
  "Hf" : m ↦s[memoize.MockMemoize :: "f"]□ f_code // [!code ++]
  --------------------------------------□
  "HΦ" : ∀ l : loc, own_mock_memoize l f -∗ Φ (# l)
  "f" : f_ptr ↦ f_code
  "Hf" : m ↦s[memoize.MockMemoize :: "f"] f_code // [!code --]
  --------------------------------------∗
  |={⊤}=> Φ (# m)
```

::::

The use of `iPersist` above has turned our regular points-to (for a struct field) into a persistent fact. We can never write to that field again in the proof, but in exchange the assertion is persistent.

```rocq
  iModIntro. iApply "HΦ".
  (* `iFrame` doesn't use the persistent context by default (for performance
  reasons primarily), but we can ask it to by passing `#` as an argument. *)
  iFrame "#".
Qed.

```

Once an `own_mock_memoize` is set up, using it is very straightforward.

```rocq
Lemma wp_MockMemoize__Call l f (x0: w64) :
  {{{ is_pkg_init memoize ∗ own_mock_memoize l f }}}
    l @ memoize @ "MockMemoize'ptr" @ "Call" #x0
  {{{ RET #(f x0); True }}}.
Proof.
  wp_start as "#Hm". iNamed "Hm".
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  goGlobalsGS0 : goGlobalsGS Σ
  l : loc
  f : w64 → w64
  x0 : w64
  Φ : val → iPropI Σ
  f_code : func.t
  ============================
  _ : is_pkg_init memoize
  "Hf" : l ↦s[memoize.MockMemoize :: "f"]□ f_code
  "Hf_spec" : fun_implements f_code f
  --------------------------------------□
  "HΦ" : True -∗ Φ (# (f x0))
  --------------------------------------∗
  WP exception_do
       (let: "m" := alloc (# l) in
        let: "x" := alloc (# x0) in
        return: (let: "$a0" := ![# uint64T] "x" in
                 ![# funcT] (struct.field_ref (# memoize.MockMemoize)
                               (# "f"%go) ![# ptrT] "m")
                   "$a0"))
  {{ v, Φ v }}
```

::::

```rocq
  wp_auto.

```

Observe how in the next line we use a Hoare triple that comes _from the persistent_ context. The correctness of `f` isn't coming from a Coq lemma, but from within separation logic.

(Unfolding `fun_implements` isn't required, it's only there to show you the definition in the goal.)

```rocq
  rewrite /fun_implements. wp_apply "Hf_spec".
```

:::: info Goal diff

```txt title="goal diff"
  Σ : gFunctors
  hG : heapGS Σ
  goGlobalsGS0 : goGlobalsGS Σ
  l : loc
  f : w64 → w64
  x0 : w64
  Φ : val → iPropI Σ
  f_code : func.t
  m_ptr, x_ptr : loc
  ============================
  _ : is_pkg_init memoize
  "Hf" : l ↦s[memoize.MockMemoize :: "f"]□ f_code
  "Hf_spec" : ∀ x : w64,
                {{{ True }}} # f_code (# x) {{{ RET # (f x); True }}}
  --------------------------------------□
  "HΦ" : True -∗ Φ (# (f x0))
  "m" : m_ptr ↦ l
  "x" : x_ptr ↦ x0
  --------------------------------------∗
  WP exception_do (return: # f_code (# x0)) {{ v, Φ v }} // [!code --]
  Φ (# (f x0)) // [!code ++]
```

::::

```rocq
  iApply "HΦ". done.
Qed.

```

### Memoize proof

Now we'll provide the same interface, but with actual memoization.

```rocq
Definition own_memoize (m: memoize.Memoize.t) (f: w64 → w64) : iProp Σ :=
   ∃ (f_code: func.t) (m_ref: loc) (results: gmap w64 w64),
     (* Notice that the map is modeled as a location. This reflects how Go maps
     work (the value of that pointer does not change as you update the map). *)
     "%Hmeq" :: ⌜m = {| memoize.Memoize.f' := f_code;
                        memoize.Memoize.results' := m_ref |}⌝ ∗
     "#Hf_spec" :: fun_implements f_code f ∗
     "Hm" :: own_map m_ref (DfracOwn 1) results ∗
     (* This is the invariant that gives the correctness of the
     memoization. *)
     "%Hresults" :: ⌜∀ x y, results !! x = Some y → y = f x⌝.

Lemma wp_NewMemoize (f: w64 → w64) (f_code: func.t) :
  {{{ is_pkg_init memoize ∗ fun_implements f_code f }}}
    memoize @ "NewMemoize" #f_code
  {{{ (v: memoize.Memoize.t), RET #v; own_memoize v f }}}.
Proof.
  wp_start as "#Hf".
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  goGlobalsGS0 : goGlobalsGS Σ
  f : w64 → w64
  f_code : func.t
  Φ : val → iPropI Σ
  ============================
  _ : is_pkg_init memoize
  "Hf" : fun_implements f_code f
  --------------------------------------□
  "HΦ" : ∀ v : memoize.Memoize.t, own_memoize v f -∗ Φ (# v)
  --------------------------------------∗
  WP exception_do
       (let: "f" := alloc (# f_code) in
        return: (let: "$f" := ![# funcT] "f" in
                 let: "$results" := map.make (# uint64T) (# uint64T) in
                 struct.make (# memoize.Memoize)
                   (list.Cons (# "f"%go, "$f")
                      (list.Cons (# "results"%go, "$results") (alist_val [])))))
  {{ v, Φ v }}
```

::::

```rocq
  wp_auto.
  wp_apply (wp_map_make) as "%m_ref Hm".
  { auto. }
  iApply "HΦ".
  iFrame "Hf Hm".
  iPureIntro.
  split; auto.
  intros x y Hget. rewrite lookup_empty in Hget.
  congruence.
Qed.

Lemma wp_Memoize__Call v f (x0: w64) :
  {{{ is_pkg_init memoize ∗ own_memoize v f }}}
    v @ memoize @ "Memoize" @ "Call" #x0
  {{{ RET #(f x0); own_memoize v f }}}.
Proof.
  wp_start as "Hm".
  iNamed "Hm". subst.
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  goGlobalsGS0 : goGlobalsGS Σ
  f : w64 → w64
  x0 : w64
  Φ : val → iPropI Σ
  f_code : func.t
  m_ref : loc
  results : gmap w64 w64
  Hresults : ∀ x y : w64, results !! x = Some y → y = f x
  ============================
  _ : is_pkg_init memoize
  "Hf_spec" : fun_implements f_code f
  --------------------------------------□
  "Hm" : m_ref ↦$ results
  "HΦ" : own_memoize
           {|
             memoize.Memoize.f' := f_code; memoize.Memoize.results' := m_ref
           |} f -∗
         Φ (# (f x0))
  --------------------------------------∗
  WP exception_do
       (let: "m" := alloc
                      (#
                         {|
                           memoize.Memoize.f' := f_code;
                           memoize.Memoize.results' := m_ref
                         |}) in
        let: "x" := alloc (# x0) in
        let: "ok" := alloc (type.zero_val (# boolT)) in
        let: "cached" := alloc (type.zero_val (# uint64T)) in
        let: "__p" := map.get
                        ![type.mapT (# uint64T) (# uint64T)]
                        (struct.field_ref (# memoize.Memoize)
                           (# "results"%go) "m")
                        ![# uint64T] "x" in
        let: "$ret0" := Fst "__p" in
        let: "$ret1" := Snd "__p" in
        let: "$r0" := "$ret0" in
        let: "$r1" := "$ret1" in
        (do: "cached" <-[# uint64T] "$r0") ;;;
        (do: "ok" <-[# boolT] "$r1") ;;;
        (if: ![# boolT] "ok" then return: ![# uint64T] "cached" else do: # ()) ;;;
        let: "y" := alloc (type.zero_val (# uint64T)) in
        let: "$r0" := let: "$a0" := ![# uint64T] "x" in
                      ![# funcT] (struct.field_ref
                                    (# memoize.Memoize)
                                    (# "f"%go) "m")
                        "$a0" in
        (do: "y" <-[# uint64T] "$r0") ;;;
        let: "$r0" := ![# uint64T] "y" in
        (do: map.insert
               ![type.mapT (# uint64T) (# uint64T)]
               (struct.field_ref (# memoize.Memoize) (# "results"%go) "m")
               ![# uint64T] "x" "$r0") ;;;
        return: ![# uint64T] "y")
  {{ v, Φ v }}
```

::::

```rocq
  wp_auto.
  cbn [memoize.Memoize.results'].
  wp_apply (wp_map_get with "Hm") as "Hm".
  wp_if_destruct; subst; try wp_auto.
  - destruct i as [y Hget].
    assert (y = f x0) by eauto; subst.
    rewrite Hget.
    iApply "HΦ".
    iFrame "#∗".
    iPureIntro.
    auto.
  - cbn [memoize.Memoize.f'].
    wp_apply "Hf_spec".
    wp_apply (wp_map_insert with "Hm") as "Hm".
    iApply "HΦ".
    iFrame "#∗".
    iSplit; [ eauto | ].
    iPureIntro.
    intros x y.
    intros Hget.
    destruct (decide (x0 = x)); subst.
    { rewrite lookup_insert in Hget. congruence. }
    rewrite lookup_insert_ne // in Hget.
    eauto.
Qed.

```

It helps to see what it looks like to use this specification (what we call a "client" of the specification in general).

The code has two such examples: `UseMemoize1` memoizes a straightforward function, while `UseMemoize2` is a bit more complicated. Both implementations internally use `std.Assert`, so we will simply prove the postcondition `True`, which shows those assertions succeed and nothing else.

```rocq
Lemma wp_UseMemoize1 :
  {{{ is_pkg_init memoize }}}
    memoize @ "UseMemoize1" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "_".
  wp_auto.

```

Setting up the memoization is the most interesting part of the proof. To use the spec, we have to both supply a pure function that the function implements (it's `λ x, word.mul x x` in this case) and prove that it actually implements that function (the proof that immediately follows in curly braces).

```rocq
  wp_apply (wp_NewMemoize (λ x, word.mul x x)).
  {
    rewrite /fun_implements.
    iIntros (x).
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  goGlobalsGS0 : goGlobalsGS Σ
  Φ : val → iPropI Σ
  m_ptr : loc
  x : w64
  ============================
  _ : is_pkg_init memoize
  --------------------------------------□
  {{{ True }}}
    #
      {|
        func.f := <>;
        func.x := "x";
        func.e :=
          exception_do
            (let: "x" := alloc "x" in
             return: ![# uint64T] "x" * ![# uint64T] "x")
      |} (# x)
  {{{ RET # (word.mul x x); True }}}
```

::::

It's somewhat subtle but the proof at this point is a Hoare triple inside separation logic (you can tell because of the `------∗` line). `wp_start` knows how to handle this so you can use it in the same way.

```rocq
    wp_start as "_".
    wp_auto.
    iApply "HΦ". done.
  }
  iIntros (v) "Hm".
  wp_auto.
  wp_apply (wp_Memoize__Call with "[$Hm]") as "Hm".
  wp_apply wp_Assert.
  { rewrite bool_decide_eq_true_2 //. }
  wp_apply (wp_Memoize__Call with "[$Hm]") as "Hm".
  wp_apply wp_Assert.
  { rewrite bool_decide_eq_true_2 //. }
  wp_apply (wp_Memoize__Call with "[$Hm]") as "Hm".
  wp_apply wp_Assert.
  { rewrite bool_decide_eq_true_2 //. }
  iApply "HΦ".
  done.
Qed.

```

The second example is more interesting because the function we're memoizing doesn't _seem_ to be pure: it refers to the `s` slice passed to `UseMemoize2`.

Nonetheless in the context of the function we can give it a pure specification, in terms of the values of that slice.

To prove the Hoare triple we will need to make the slice read-only. This will turn `own_slice_small s uint64T (DfracOwn 1) xs` into `own_slice_small s uint64T DfracDiscarded xs` - the special fraction `DfracDiscarded` is how the implementation represents a persistent assertion. This is just like turning `l ↦[uint64T] v` into `l ↦[uint64T]□ v` - the fraction in `own_slice_small` plays the same role as it does for points-to assertions.

Think about what would happen we didn't make the slice read-only. When we call `NewMemoize` we can prove the function sums the list `[x1; x2; x3]`, since that's the initial value of the slice elements. If the slice were read-write, after `NewMemoize`, we could then change the slice, at which point it would no longer sum `[x1; x2; x3]`, and `Call` would no longer work as specified above.

```rocq
(* don't worry too much about how this is defined; it's standard functional programming list stuff (read up on [foldl] and [foldr] if you're interested) *)
Definition list_w64_sum : list w64 → w64 :=
  foldl word.add (W64 0).

Lemma list_w64_sum_app1 (xs: list w64) (x: w64) :
  list_w64_sum (xs ++ [x]) = word.add (list_w64_sum xs) x.
Proof.
  rewrite /list_w64_sum.
  rewrite foldl_app //.
Qed.

Lemma wp_UseMemoize2 (s: slice.t) (x1 x2 x3: w64) :
  {{{ is_pkg_init memoize ∗ own_slice s (DfracOwn 1) [x1; x2; x3] }}}
    memoize @ "UseMemoize2" #s
  {{{ RET #(); True }}}.
Proof.
  wp_start as "Hs".
  wp_auto.
  iDestruct (own_slice_len with "Hs") as %Hsz.
  iMod (own_slice_persist with "Hs") as "#Hs".
  iPersist "s".
  simpl in Hsz.

  wp_apply (wp_NewMemoize (λ (x: w64),
                if decide (uint.Z x ≤ 3) then
                  list_w64_sum (take (uint.nat x) [x1; x2; x3])
                else W64 0
           )).
  {
    rewrite /fun_implements. iIntros (n).
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  goGlobalsGS0 : goGlobalsGS Σ
  s : slice.t
  x1, x2, x3 : w64
  Φ : val → iPropI Σ
  s_ptr, sumUpto_ptr, m_ptr : loc
  Hsz : 3%nat = uint.nat (slice.len_f s)
  n : w64
  ============================
  _ : is_pkg_init memoize
  "Hs" : s ↦*□ [x1; x2; x3]
  "s" : s_ptr ↦□ s
  --------------------------------------□
  {{{ True }}}
    #
      {|
        func.f := <>;
        func.x := "n";
        func.e :=
          exception_do
            (let: "n" := alloc "n" in
             (if: ![# uint64T] "n" >
                  s_to_w64 (let: "$a0" := ![# sliceT] (# s_ptr) in
                            slice.len "$a0")
              then return: # (W64 0) else do: # ()) ;;;
             let: "sum" := alloc (type.zero_val (# uint64T)) in
             (let: "i" := alloc (type.zero_val (# uint64T)) in
              let: "$r0" := # (W64 0) in
              (do: "i" <-[# uint64T] "$r0") ;;;
              for: (λ: <>, ![# uint64T] "n" > ![# uint64T] "i") ;
              (λ: <>, do: "i" <-[# uint64T] ![# uint64T] "i" + # (W64 1)) :=
                λ: <>,
                  do: "sum" <-[# uint64T] ![# uint64T] "sum" +
                                          ![# uint64T]
                                          (slice.elem_ref
                                             (# uint64T)
                                             ![# sliceT]
                                             (# s_ptr) ![
                                             # uint64T] "i")) ;;;
             return: ![# uint64T] "sum")
      |} (# n)
  {{{ RET #
            (if decide (uint.Z n ≤ 3)
             then list_w64_sum (take (uint.nat n) [x1; x2; x3])
             else W64 0);
      True }}}
```

::::

Notice how the slice is available in the persistent context for this Hoare triple - this is only possible because we made it persistent and thus promised (for the duration of the proof) not to write to it.

The rest of this proof is general loop and slice reasoning and not related to this specific example.

```rocq
    wp_start as "_".
    wp_auto.
    wp_if_destruct.
    { simpl in Hsz.
      rewrite -> decide_False by word.
      iApply "HΦ"; done.
    }
    wp_auto.
    iAssert (
        ∃ (i: w64),
          "i" :: i_ptr ↦ i ∗
          "%Hi" :: ⌜0 ≤ uint.Z i ≤ uint.Z n⌝ ∗
       "sum" :: sum_ptr ↦ (list_w64_sum (take (uint.nat i) [x1; x2; x3]))
      )%I with "[$i $sum]" as "HI".
    { iPureIntro. word. }
    wp_for "HI".
    wp_if_destruct; try wp_auto.
    - wp_pure.
      { word. }
      list_elem [x1; x2; x3] i as x_i.
      wp_apply (wp_load_slice_elem with "[$Hs]") as "_"; [ by eauto | ].
      wp_for_post.
      iFrame.
      iSplit.
      { iPureIntro. word. }
      replace (uint.nat (word.add i (W64 1))) with (S (uint.nat i)) by word.
      erewrite take_S_r; eauto.
      rewrite list_w64_sum_app1.
      iFrame "sum".
    -
```

The little proof pattern below of using `iExactEq` is sometimes useful - it allows you to use any `"H": P` to prove `Q` if you can prove `P = Q`. This often has to be paired with `repeat f_equal` since you'll otherwise have `#(...) = #(...)` and you generally want to get rid of the `#` function in front of both sides.

```rocq
      iDestruct ("HΦ" with "[]") as "HΦ".
      { done. }
      iExactEq "HΦ"; repeat f_equal.
      rewrite -> decide_True by word.
      replace (uint.Z i) with (uint.Z n) by word.
      auto.
  }

  iIntros (m) "Hm".
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  goGlobalsGS0 : goGlobalsGS Σ
  s : slice.t
  x1, x2, x3 : w64
  Φ : val → iPropI Σ
  s_ptr, sumUpto_ptr, m_ptr : loc
  Hsz : 3%nat = uint.nat (slice.len_f s)
  m : memoize.Memoize.t
  ============================
  _ : is_pkg_init memoize
  "Hs" : s ↦*□ [x1; x2; x3]
  "s" : s_ptr ↦□ s
  --------------------------------------□
  "HΦ" : True -∗ Φ (# ())
  "sumUpto" : sumUpto_ptr ↦ {|
                              func.f := <>;
                              func.x := "n";
                              func.e :=
                                exception_do
                                  (let: "n" := alloc "n" in
                                   (if: ![# uint64T] "n" >
                                        s_to_w64 (let: "$a0" :=
                                                 ![
                                                 # sliceT]
                                                 (# s_ptr) in
                                                 slice.len "$a0")
                                    then return: # (W64 0) else do:
                                    # ()) ;;;
                                   let: "sum" := alloc
                                                 (type.zero_val (# uint64T)) in
                                   (let: "i" := alloc
                                                 (type.zero_val (# uint64T)) in
                                    let: "$r0" :=
                                    # (W64 0) in
                                    (do: "i" <-[# uint64T] "$r0") ;;;
                                    for: (λ: <>,
                                            ![# uint64T] "n" >
                                            ![# uint64T] "i") ;
                                    (λ: <>,
                                       do: "i" <-[
                                           # uint64T]
                                           ![# uint64T] "i" +
                                           # (W64 1)) :=
                                      λ: <>,
                                        do: "sum" <-[
                                            # uint64T]
                                            ![# uint64T] "sum" +
                                            ![# uint64T]
                                            (slice.elem_ref
                                               (# uint64T)
                                               ![# sliceT]
                                               (# s_ptr) ![
                                               # uint64T] "i")) ;;;
                                   return: ![# uint64T] "sum")%E
                            |}
  "m" : m_ptr ↦ default_val memoize.Memoize.t
  "Hm" : own_memoize m
           (λ x : w64,
              if decide (uint.Z x ≤ 3)
              then list_w64_sum (take (uint.nat x) [x1; x2; x3])
              else W64 0)
  --------------------------------------∗
  WP exception_do
       (let: "$r0" := # m in
        (do: # m_ptr <-[# memoize.Memoize] "$r0") ;;;
        let: "y1" := alloc (type.zero_val (# uint64T)) in
        let: "$r0" := let: "$a0" := # (W64 3) in
                      method_call (# memoize) (# "Memoize"%go)
                        (# "Call"%go) ![# memoize.Memoize]
                        (# m_ptr) "$a0" in
        (do: "y1" <-[# uint64T] "$r0") ;;;
        let: "y2" := alloc (type.zero_val (# uint64T)) in
        let: "$r0" := let: "$a0" := # (W64 3) in
                      method_call (# memoize) (# "Memoize"%go)
                        (# "Call"%go) ![# memoize.Memoize]
                        (# m_ptr) "$a0" in
        (do: "y2" <-[# uint64T] "$r0") ;;;
        (do: (let: "$a0" := ![# uint64T] "y1" = ![# uint64T] "y2" in
              func_call (# std) (# "Assert"%go) "$a0")) ;;;
        return: # ())
  {{ v, Φ v }}
```

::::

Here we come back from calling `NewMemoize`. As in `UseMemoize1`, all the hard work is done and calling the new object is easy.

```rocq
  wp_auto.
  wp_apply (wp_Memoize__Call with "[$Hm]") as "Hm".
  wp_apply (wp_Memoize__Call with "[$Hm]") as "Hm".
  wp_apply (wp_Assert).
  { rewrite bool_decide_eq_true_2 //. }
  iApply "HΦ". done.
Qed.

End proof.
```
