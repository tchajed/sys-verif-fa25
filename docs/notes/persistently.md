---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture
tags: literate
order: 15
shortTitle: "Lecture 15: Persistently"
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Lecture 15: The persistently modality

> Follow these notes in Coq at [src/sys_verif/program_proof/persistently.v](https://github.com/tchajed/sys-verif-fa24-proofs/blob/main/src/sys_verif/program_proof/persistently.v).

## Learning outcomes

- Appreciate the value of having persistent propositions.
- Explain the difference between a Hoare triple as a Prop and as an iProp.

## Motivation

We know that separation logic propositions are generally not duplicable ($P \nvdash P \sep P$). This is because we interpret propositions as asserting exclusive ownership, for example over heap locations. However, ownership does not _have_ to be exclusive. We've already seen one example with pure propositions $\lift{\phi}$, which can be freely duplicated and in the IPM even moved out of the spatial context into the Coq context. Another example where ownership isn't exlusive is if a pointer is _read-only_, it is safe to have many copies of its points-to fact, as long as those assertions are used only for reading and not writing.

Before getting into modalities, let's revisit the mechanisms in Coq for read-only pointers.

```coq
From sys_verif.program_proof Require Import prelude empty_ffi.
From Goose.sys_verif_code Require Import memoize.

Section proof.
Context `{hG: !heapGS Σ}.

```

## Read-only pointers

We saw in a previous lecture, and in the [fractions guide](/notes/program-proofs/fractions.md), how _fractional permissions_ can be used for read-only access.

Recall the basic splitting/recombining rule:

$l ↦_{q_1 + q_2} v ⊣⊢ l ↦_{q_1} v ∗ l ↦_{q_2} v$

We can see splitting at work in this example, which first splits the assertion `l ↦[uint64T] #x` (using `iDestruct`, which knows to split a fractional points-to into two halves), then uses the two halves for the two loads.

Fractions also support _combining_ to recover full ownership and go back to being able to write to the pointer.

```coq
Lemma split_fraction_example (l: loc) (x: w64) :
  {{{ l ↦[uint64T] #x ∗ ⌜uint.Z x < 100⌝ }}}
    let: "y" := ![uint64T] #l in
    let: "z" := ![uint64T] #l in
    #l <-[uint64T] ("y" + "z")
  {{{ RET #(); l ↦[uint64T] #(LitInt (word.add x x)) }}}.
Proof.
  wp_start as "H".
  iDestruct "H" as "[Hx %Hbound]".
  iDestruct "Hx" as "[Hx1 Hx2]".
```

:::: info Goal diff

```txt title="goal diff"
  Σ : gFunctors
  hG : heapGS Σ
  l : loc
  x : w64
  Φ : val → iPropI Σ
  Hbound : uint.Z x < 100
  ============================
  "Hx" : l ↦[uint64T] #x // [!code --]
  "Hx1" : l ↦[uint64T]{#1 / 2} #x // [!code ++]
  "Hx2" : l ↦[uint64T]{#1 / 2} #x // [!code ++]
  "HΦ" : ▷ (l ↦[uint64T] #(word.add x x) -∗ Φ #())
  --------------------------------------∗
  WP let: "y" := ![uint64T] #l in
     let: "z" := ![uint64T] #l in #l <-[uint64T] "y" + "z"
  {{ v, Φ v }}
```

::::

```coq
  wp_apply (wp_LoadAt with "[$Hx1]"). iIntros "Hx1".
  wp_apply (wp_LoadAt with "[$Hx2]"). iIntros "Hx2".
  iCombine "Hx1 Hx2" as "Hx".
```

:::: info Goal diff

```txt title="goal diff"
  Σ : gFunctors
  hG : heapGS Σ
  l : loc
  x : w64
  Φ : val → iPropI Σ
  Hbound : uint.Z x < 100
  ============================
  "HΦ" : l ↦[uint64T] #(word.add x x) -∗ Φ #()
  "Hx1" : l ↦[uint64T]{#1 / 2} #x // [!code --]
  "Hx2" : l ↦[uint64T]{#1 / 2} #x // [!code --]
  "Hx" : l ↦[uint64T] #x // [!code ++]
  --------------------------------------∗
  WP let: "z" := #x in #l <-[uint64T] #x + "z" {{ v, Φ v }}
```

::::

```coq
  wp_store.
  iModIntro.
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

```coq
Lemma alloc_ro_spec (x: w64) :
  {{{ True }}}
    ref_to uint64T #x
  {{{ (l: loc), RET (#l: val); l ↦[uint64T]□ #x }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  rewrite -wp_fupd.
  wp_alloc l as "H".

```

This is the step where we persist the points-to permission and turn it into a persistent, read-only fact. Using `struct_pointsto_persist` requires the `iMod` tactic, which we will cover later when we talk about concurrency; for now think of it as a variation on `iDestruct`.

```coq
  iMod (struct_pointsto_persist with "H") as "#Hro".
```

:::: info Goal diff

```txt title="goal diff"
  Σ : gFunctors
  hG : heapGS Σ
  x : w64
  Φ : val → iPropI Σ
  l : loc
  ============================
  "Hro" : l ↦[uint64T]□ #x // [!code ++]
  --------------------------------------□ // [!code ++]
  "HΦ" : ∀ l0 : loc, l0 ↦[uint64T]□ #x -∗ Φ #l0
  "H" : l ↦[uint64T] #x // [!code --]
  --------------------------------------∗
  |={⊤}=> Φ #l
```

::::

Notice from the goal diff that the output (renamed to "Hro" for clarity) is put into a separate list of hypotheses - this is the persistent context.

To obtain the persistent points-to assertion, we have to give up the regular fractional assertion, and this operation is _not_ reversible - the persistence relies on the location never being written to.

```coq
  iModIntro.
  iApply "HΦ".
  iFrame "Hro".
Qed.

```

With a persistent permission, it's reasonable (and expected) that the permission need not be returned in the postcondition.

```coq
Lemma read_discarded_spec (l: loc) (x: w64) :
  {{{ l ↦[uint64T]□ #x }}}
    ![uint64T] #l
  {{{ RET #x; True }}}.
Proof.
  wp_start as "#H".
  wp_apply (wp_LoadAt with "[$H]"). iIntros "_".
  iApply "HΦ". auto.
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

You should start by quickly reading the code for this example at [go/memoize/memoize.go](https://github.com/tchajed/sys-verif-fa24-proofs/blob/main/go/memoize/memoize.go).

### MockMemoize proof

As a warmup, we'll verify the "MockMemoize" implementation. This version still has to store and call the function, but there's no memoization happening - when we use `m.Call(x)` it just always calls `f(x)`.

There is another difference between the two implementations: we use a `*MockMemoize` whereas we'll use `Memoize` - one is always used through a pointer, while the other is used as a value. Both would work in this case, we're just illustrating what this looks like in the proofs.

---

To give a specification to the memoization library, we will require that the user prove that the provided function, which we'll call `f_code` (of type `val`, since it's a function in GooseLang), implements a Gallina function `f : w64 → w64`. This is more restrictive than strictly necessary, but we do need it to have some Hoare triple, since it must at minimum be safe to call, and if we want to say anything about the result of `Call` we also need to know what it does. The choice here is to require it to implement some pure function over integers, but which is one is arbitrary.

The core of the proof is the representation invariant for a `*MockMemoize`. The most interesting part of that invariant is how we say that `f_code` implements `f: w64 → w64`.

```coq
Definition fun_implements (f_code: val) (f: w64 → w64) : iProp Σ :=
  ∀ (x:w64), {{{ True }}} f_code #x {{{ RET #(f x); True }}}.

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

```coq
Definition own_mock_memoize (m: loc) (f: w64 → w64) : iProp Σ :=
   ∃ (f_code: val),
     "#Hf" :: m ↦[MockMemoize :: "f"]□ f_code ∗
     "#Hf_spec" :: fun_implements f_code f.

Lemma wp_NewMockMemoize (f_code: val) (f: w64 → w64) :
  (* NOTE: this val_ty is an unnecessary restriction in Goose *)
  val_ty f_code (arrowT uint64T uint64T) →
  {{{ fun_implements f_code f }}}
    NewMockMemoize f_code
  {{{ l, RET #l; own_mock_memoize l f }}}.
Proof.
  intros Hty.
  wp_start as "#Hf".
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  f_code : val
  f : w64 → w64
  Hty : val_ty f_code (uint64T -> uint64T)
  Φ : val → iPropI Σ
  ============================
  "Hf" : fun_implements f_code f
  --------------------------------------□
  "HΦ" : ∀ l : loc, own_mock_memoize l f -∗ Φ #l
  --------------------------------------∗
  WP struct.alloc MockMemoize (f_code, #()) {{ v, Φ v }}
```

::::

```coq
  wp_pures.
  (* NOTE: [wp_apply] will lose the |==> (update) modality here, but we can add
  it ourselves with this rewrite. *)
  rewrite -wp_fupd.
  wp_alloc m as "Hm".
  iApply struct_fields_split in "Hm". iNamed "Hm".
  iMod (struct_field_pointsto_persist with "f") as "#f".
```

:::: info Goal diff

```txt title="goal diff"
  Σ : gFunctors
  hG : heapGS Σ
  f_code : val
  f : w64 → w64
  Hty : val_ty f_code (uint64T -> uint64T)
  Φ : val → iPropI Σ
  m : loc
  ============================
  "Hf" : fun_implements f_code f
  "f" : m ↦[MockMemoize::"f"]□ f_code // [!code ++]
  --------------------------------------□
  "HΦ" : ∀ l : loc, own_mock_memoize l f -∗ Φ #l
  "f" : m ↦[MockMemoize::"f"] f_code // [!code --]
  --------------------------------------∗
  |={⊤}=> Φ #m
```

::::

The use of `iMod` above has turned our regular points-to (for a struct field) into a persistent fact. We can never write to that field again in the proof, but in exchange the assertion is persistent.

```coq
  iModIntro. iApply "HΦ".
  (* `iFrame` doesn't use the persistent context by default (for performance
  reasons primarily), but we can ask it to by passing `#` as an argument. *)
  iFrame "#".
Qed.

```

Once an `own_mock_memoize` is set up, using it is very straightforward.

```coq
Lemma wp_MockMemoize__Call l f (x0: w64) :
  {{{ own_mock_memoize l f }}}
    MockMemoize__Call #l #x0
  {{{ RET #(f x0); True }}}.
Proof.
  wp_start as "#Hm". iNamed "Hm".
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  l : loc
  f : w64 → w64
  x0 : w64
  Φ : val → iPropI Σ
  f_code : val
  ============================
  "Hf" : l ↦[MockMemoize::"f"]□ f_code
  "Hf_spec" : fun_implements f_code f
  --------------------------------------□
  "HΦ" : True -∗ Φ #(f x0)
  --------------------------------------∗
  WP let: "x" := #x0 in struct.loadF MockMemoize "f" #l "x" {{ v, Φ v }}
```

::::

```coq
  wp_pures.
  wp_loadField.

```

Observe how in the next line we use a Hoare triple that comes _from the persistent_ context. The correctness of `f` isn't coming from a Coq lemma, but from within separation logic.

(Unfolding `fun_implements` isn't required, it's only there to show you the definition in the goal.)

```coq
  rewrite /fun_implements. wp_apply "Hf_spec".
```

:::: info Goal diff

```txt title="goal diff"
  Σ : gFunctors
  hG : heapGS Σ
  l : loc
  f : w64 → w64
  x0 : w64
  Φ : val → iPropI Σ
  f_code : val
  ============================
  "Hf" : l ↦[MockMemoize::"f"]□ f_code
  "Hf_spec" : ∀ x : w64, {{{ True }}} f_code #x {{{ RET #(f x); True }}}
  --------------------------------------□
  "HΦ" : True -∗ Φ #(f x0)
  --------------------------------------∗
  WP f_code #x0 {{ v, Φ v }} // [!code --]
  Φ #(f x0) // [!code ++]
```

::::

```coq
  iApply "HΦ". done.
Qed.

```

### Memoize proof

Now we'll provide the same interface, but with actual memoization.

```coq
Definition own_memoize (m: val) (f: w64 → w64) : iProp Σ :=
   ∃ (f_code: val) (m_ref: loc) (results: gmap w64 w64),
     (* Notice that the map is modeled as a location. This reflects how Go maps
     work (the value of that pointer does not change as you update the map). *)
     "%Hmeq" :: ⌜m = (f_code, (#m_ref, #()))%V⌝ ∗
     "#Hf_spec" :: fun_implements f_code f ∗
     "Hm" :: own_map m_ref (DfracOwn 1) results ∗
     (* This is the invariant that gives the correctness of the
     memoization. *)
     "%Hresults" :: ⌜∀ x y, results !! x = Some y → y = f x⌝.

Lemma wp_NewMemoize (f: w64 → w64) (f_code: val) :
  {{{ fun_implements f_code f }}}
    NewMemoize f_code
  {{{ v, RET v; own_memoize v f }}}.
Proof.
  wp_start as "#Hf".
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  f : w64 → w64
  f_code : val
  Φ : val → iPropI Σ
  ============================
  "Hf" : fun_implements f_code f
  --------------------------------------□
  "HΦ" : ∀ v : val, own_memoize v f -∗ Φ v
  --------------------------------------∗
  WP (f_code, (NewMap uint64T uint64T #(), #())) {{ v, Φ v }}
```

::::

```coq
  wp_apply (wp_NewMap w64). iIntros (m_ref) "Hm".
  wp_pures.
  iModIntro. iApply "HΦ".
  iFrame "Hf Hm".
  iPureIntro.
  split; auto.
  intros x y Hget. rewrite lookup_empty in Hget.
  congruence.
Qed.

Lemma wp_Memoize__Call v f (x0: w64) :
  {{{ own_memoize v f }}}
    Memoize__Call v #x0
  {{{ RET #(f x0); own_memoize v f }}}.
Proof.
  wp_start as "Hm".
  iNamed "Hm". subst.
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  f : w64 → w64
  x0 : w64
  Φ : val → iPropI Σ
  f_code : val
  m_ref : loc
  results : gmap w64 w64
  Hresults : ∀ x y : w64, results !! x = Some y → y = f x
  ============================
  "Hf_spec" : fun_implements f_code f
  --------------------------------------□
  "Hm" : own_map m_ref (DfracOwn 1) results
  "HΦ" : own_memoize (f_code, (#m_ref, #())) f -∗ Φ #(f x0)
  --------------------------------------∗
  WP let: "x" := #x0 in
     let: "__p" := impl.MapGet
                     ((λ: "v", (λ: "v", Fst "v")%V (Snd "v"))%V
                        (f_code, (#m_ref, #()))%V) "x" in
     let: "cached" := Fst "__p" in
     let: "ok" := Snd "__p" in
     if: "ok" then "cached"
     else let: "y" := (λ: "v", Fst "v")%V (f_code, (#m_ref, #()))%V "x" in
          impl.MapInsert
            ((λ: "v", (λ: "v", Fst "v")%V (Snd "v"))%V
               (f_code, (#m_ref, #()))%V) "x" "y";; "y"
  {{ v, Φ v }}
```

::::

```coq
  wp_pures.
  wp_apply (wp_MapGet with "Hm"). iIntros (v ok) "[%Hmap_get Hm]".
  wp_pures.
  wp_if_destruct; subst.
  - apply map_get_true in Hmap_get.
    iModIntro.
    replace v with (f x0).
    { iApply "HΦ". iFrame "#∗". eauto. }
    apply Hresults in Hmap_get; auto.
  - wp_pures.
    wp_apply "Hf_spec". wp_pures.
    wp_apply (wp_MapInsert with "Hm").
    { auto. }
    iIntros "Hm".
    rewrite /map_insert.
    wp_pures.
    iModIntro.
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

The code has two such examples: `UseMemoize1` memoizes a straightforward function, while `UseMemoize2` is a bit more complicated. Both implementations internally use `primitive.Assert`, so we will simply prove the postcondition `True`, which shows those assertions succeed and nothing else.

```coq
Lemma wp_UseMemoize1 :
  {{{ True }}}
    UseMemoize1 #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "_".


```

Setting up the memoization is the most interesting part of the proof. To use the spec, we have to both supply a pure function that the function implements (it's `λ x, word.mul x x` in this case) and prove that it actually implements that function (the proof that immediately follows in curly braces).

```coq
  wp_apply (wp_NewMemoize (λ x, word.mul x x)).
  {
    rewrite /fun_implements.
    iIntros (x).
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  Φ : val → iPropI Σ
  x : w64
  ============================
  --------------------------------------∗
  {{{ True }}} (λ: "x", "x" * "x")%V #x {{{ RET #(word.mul x x); True }}}
```

::::

It's somewhat subtle but the proof at this point is a Hoare triple inside separation logic (you can tell because of the `------∗` line). `wp_start` knows how to handle this so you can use it in the same way.

```coq
    wp_start as "_".
    wp_pures.
    iModIntro. iApply "HΦ". done.
  }

  iIntros (v) "Hm".
  wp_pures.
  wp_apply (wp_Memoize__Call with "[$Hm]"). iIntros "Hm".
  wp_pures.
  wp_apply wp_Assert.
  { rewrite bool_decide_eq_true_2 //. }
  wp_pures.
  wp_apply (wp_Memoize__Call with "[$Hm]"). iIntros "Hm".
  wp_pures.
  wp_apply wp_Assert.
  { rewrite bool_decide_eq_true_2 //. }
  wp_apply (wp_Memoize__Call with "[$Hm]"). iIntros "Hm".
  wp_pures.
  wp_apply wp_Assert.
  { rewrite bool_decide_eq_true_2 //. }
  wp_pures.
  iModIntro.
  iApply "HΦ".
  done.
Qed.

```

The second example is more interesting because the function we're memoizing doesn't _seem_ to be pure: it refers to the `s` slice passed to `UseMemoize2`.

Nonetheless in the context of the function we can give it a pure specification, in terms of the values of that slice.

To prove the Hoare triple we will need to make the slice read-only. This will turn `own_slice_small s uint64T (DfracOwn 1) xs` into `own_slice_small s uint64T DfracDiscarded xs` - the special fraction `DfracDiscarded` is how the implementation represents a persistent assertion. This is just like turning `l ↦[uint64T] v` into `l ↦[uint64T]□ v` - the fraction in `own_slice_small` plays the same role as it does for points-to assertions.

Think about what would happen we didn't make the slice read-only. When we call `NewMemoize` we can prove the function sums the list `[x1; x2; x3]`, since that's the initial value of the slice elements. If the slice were read-write, after `NewMemoize`, we could then change the slice, at which point it would no longer sum `[x1; x2; x3]`, and `Call` would no longer work as specified above.

```coq
(* don't worry too much about how this is defined; it's standard functional programming list stuff (read up on [foldl] and [foldr] if you're interested) *)
Definition list_w64_sum : list w64 → w64 :=
  foldl word.add (W64 0).

Lemma list_w64_sum_app1 (xs: list w64) (x: w64) :
  list_w64_sum (xs ++ [x]) = word.add (list_w64_sum xs) x.
Proof.
  rewrite /list_w64_sum.
  rewrite foldl_app //.
Qed.

Lemma wp_UseMemoize2 (s: Slice.t) (x1 x2 x3: w64) :
  {{{ own_slice_small s uint64T (DfracOwn 1) [x1; x2; x3] }}}
    UseMemoize2 s
  {{{ RET #(); True }}}.
Proof.
  wp_start as "Hs".
  wp_pures.
  iDestruct (own_slice_small_sz with "Hs") as %Hsz.
  iMod (own_slice_small_persist with "Hs") as "#Hs".
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
  s : Slice.t
  x1, x2, x3 : w64
  Φ : val → iPropI Σ
  Hsz : 3%nat = uint.nat (Slice.sz s)
  n : w64
  ============================
  "Hs" : own_slice_small s uint64T DfracDiscarded [x1; x2; x3]
  --------------------------------------□
  {{{ True }}}
    (λ: "n",
       if: "n" > slice.len s then #(W64 0)
       else let: "sum" := ref (zero_val uint64T) in
            let: "i" := ref_to uint64T #(W64 0) in
            (for: (λ: <>, "n" > ![uint64T] "i") ;
             (λ: <>, "i" <-[uint64T] ![uint64T] "i" + #(W64 1)) :=
               λ: <>,
                 "sum" <-[uint64T] ![uint64T] "sum" +
                                   SliceGet uint64T s ![uint64T] "i";;
                 Continue);; ![uint64T] "sum")%V #n
  {{{ RET #(if decide (uint.Z n ≤ 3)
            then list_w64_sum (take (uint.nat n) [x1; x2; x3])
            else W64 0); True }}}
```

::::

Notice how the slice is available in the persistent context for this Hoare triple - this is only possible because we made it persistent and thus promised (for the duration of the proof) not to write to it.

The rest of this proof is general loop and slice reasoning and not related to this specific example.

```coq
    wp_start as "_".
    wp_apply (wp_slice_len). wp_pures.
    wp_if_destruct.
    { iModIntro.
      simpl in Hsz.
      rewrite decide_False; [ | word ].
      iApply "HΦ"; done.
    }
    wp_alloc sum_l as "sum".
    wp_alloc i_l as "i".
    wp_pures.
    wp_apply (wp_forUpto
                (λ i,
                  "sum" :: sum_l ↦[uint64T] #(list_w64_sum (take (uint.nat i) [x1; x2; x3]))
                )%I
               with "[] [$i $sum]").
    { word. }
    {  iIntros (i). wp_start as "H". iNamed "H".
       iDestruct "H" as "[i %Hlt]".
       wp_load.
       wp_load.
       list_elem [x1; x2; x3] i as x_i.
       wp_apply (wp_SliceGet with "[$Hs]").
       { eauto. }
       iIntros "_".
       wp_store.
       iModIntro. iApply "HΦ". iFrame.
       replace (uint.nat (word.add i (W64 1))) with (S (uint.nat i)) by word.
       erewrite take_S_r; eauto.
       rewrite list_w64_sum_app1.
       iExact "sum". }
    iIntros "[H Hi]". iNamed "H".
    wp_load.
    iModIntro.


```

The little proof pattern below of using `iExactEq` is sometimes useful - it allows you to use any `"H": P` to prove `Q` if you can prove `P = Q`. This often has to be paired with `repeat f_equal` since you'll otherwise have `#(...) = #(...)` and you generally want to get rid of the `#` function in front of both sides.

```coq
    iDestruct ("HΦ" with "[]") as "HΦ".
    { done. }
    iExactEq "HΦ". repeat f_equal.

    rewrite decide_True; [ | word ].
    auto.
  }

  iIntros (m) "Hm".
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  s : Slice.t
  x1, x2, x3 : w64
  Φ : val → iPropI Σ
  Hsz : 3%nat = uint.nat (Slice.sz s)
  m : val
  ============================
  "Hs" : own_slice_small s uint64T DfracDiscarded [x1; x2; x3]
  --------------------------------------□
  "HΦ" : True -∗ Φ #()
  "Hm" : own_memoize m
           (λ x : w64,
              if decide (uint.Z x ≤ 3)
              then list_w64_sum (take (uint.nat x) [x1; x2; x3])
              else W64 0)
  --------------------------------------∗
  WP let: "m" := m in
     let: "y1" := Memoize__Call "m" #(W64 3) in
     let: "y2" := Memoize__Call "m" #(W64 3) in
     impl.Assert ("y1" = "y2");; #()
  {{ v, Φ v }}
```

::::

Here we come back from calling `NewMemoize`. As in `UseMemoize1`, all the hard work is done and calling the new object is easy.

```coq
  wp_pures.
  wp_apply (wp_Memoize__Call with "[$Hm]"). iIntros "Hm".
  wp_pures.
  wp_apply (wp_Memoize__Call with "[$Hm]"). iIntros "Hm".
  wp_pures.
  wp_apply (wp_Assert).
  { rewrite bool_decide_eq_true_2 //. }
  wp_pures.
  iModIntro. iApply "HΦ". done.
Qed.

End proof.
```
