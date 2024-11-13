---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture
tags: literate
order: 19
shortTitle: "Lecture 19: Ghost state"
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Lecture 19: Ghost state

> Follow these notes in Coq at [src/sys_verif/program_proof/ghost_state.v](https://github.com/tchajed/sys-verif-fa24-proofs/blob/main/src/sys_verif/program_proof/ghost_state.v).

## Learning outcomes

1. Explain the API for a ghost variable.
2. Use ghost state for simple concurrency proofs.

<!-- @include: ./macros.snippet.md -->

## Motivation

Resource algebras gave a way to share locations among threads, at least read-only. This turns out not to be enough to prove reasonable programs; we'll have a running example of something apparently simple that requires new techniques.

Not to fear, though, since _more_ resource algebras will solve the problem. Instead of just using RAs to divide ownership of (physical) pointers, we can also use them to divide ownership of _ghost variables_ that are only created for the sake of the proof.

Ghost variables are powerful because we can define them with any RA, and the choice of RA allows the proof to decide how threads coordinate. This is a bit abstract; we'll see concretely what the API looks like and some examples in this lecture.

## Code example

```go
// Spawn runs `f` in a parallel goroutine and returns a handle. Calling Join()
// on the handle will wait for it to finish.
func Spawn(f func()) *JoinHandle { ... }

// JoinHandle is a mechanism to wait for a goroutine to finish. Calling `Join()`
// on the handle returned by `Spawn(f)` will wait for f to finish.
type JoinHandle struct {
  /* private fields */
}

func (h *JoinHandle) Join() { ... }

// ParallelAdd3 adds 2 to a shared integer from two threads, then reads the
// result.
//
// It returns 4.
//
// The 3 in the name is because there are two earlier versions of this example
// with slightly different concurrency primitives.
func ParallelAdd3() uint64 {
	m := new(sync.Mutex)
	var i uint64 = 0
	h1 := std.Spawn(func() {
		m.Lock()
		i += 2
		m.Unlock()
	})
	h2 := std.Spawn(func() {
		m.Lock()
		i += 2
		m.Unlock()
	})
	h1.Join()
	h2.Join()
	m.Lock()
	y := i
	m.Unlock()
	return y
}
```

### Exercise: come up with a lock invariant

What could the lock invariant be?

Try to come up with a lock invariant to prove that the result is exactly 4. Then, after failing to do that, come up with a lock invariant that is at least true.

## Ghost variables

### Syntax

Ghost variables build upon the general support for RAs we used to develop fractional permissions.

We need one tweak to separation logic assertions to support talking about ghost variables: instead of a single global RA $\own(a)$, which we only used to define $l \mapsto_q v$, we'll define $\own_\gamma(a : M)$ for ownership of $a$ within a ghost variable named $\gamma$ (gamma) that has type $M$, which is an RA.

Note that:

1. We can have several ghost variables, as indicated by the presence of a name (we'll see that these variables can be dynamically allocated).
2. The value of a ghost variable is an element of a resource algebra.
3. We can pick an arbitrary RA for each ghost variable, and a different one for each.

It's worth commenting right away on the difference between $\own_γ(a : M)$ and the value of the ghost variable. It's helpful to think of a ghost variable as having some global value, but ownership of that value can be subdivided according to $\own_γ(a \cdot b) ⊣⊢ \own_γ(a) ∗ \own_γ(b)$ (with the definition of $\cdot$ coming from $M$), and then those separate $\own_γ$ assertions could be divided among threads or put into lock invariants. The value of the ghost variable $γ$ is the composition of all the parts of all the threads at any given point in time.

### Creating and modifying ghost variables

An important aspect of ghost variables is when they can be changed. This is non-trivial because we can split ownership of a ghost variable, so it's important that changes in one "shard" (that is, one $\own_\gamma$) are consistent with the other shards.

To see the importance of this consistency, consider ghost variables using the fracRA from last lecture. Recall that the elements had the form $(q, v)$, and composition was defined as follows: $(q_1, v) \cdot (q_2, v) = (q_1 + q_2, v)$ and $(q_1, v_1) \cdot (q_2, v_2) = \errorval$ if $v_1 ≠ v_2$. If we split $\own_γ((1, v))$ into $\own_γ((1/2, v)) ∗ \own_γ((1/2, v))$ and change just one half to $\own_γ((1/2, v'))$, what happens?

**Exercise:** Think for a minute about what goes wrong.

::: details Solution

If at one step of the proof we had $\own_γ((1, v)) ⊢ \own_γ((1/2, v)) ∗ \own_γ((1/2), v)$ and then somehow changed one half, the other is presumably unaffected (since it is separate). Then we'd have $\own_\gamma((1/2, v')) ∗ \own_γ((1/2, v))$. These can be recombined to form $\own_γ(\errorval)$. But we know that all owned values are valid, so we have now proven $\lift{\False}$. If a program proof could take this action, it could prove anything, and we know that this would make separation logic unsound.

:::

The rule for changing ghost variables is that the allowed changes are _frame-preserving updates_. A frame-preserving update $a \mupd b$ is one where $∀ r, \valid (a \cdot r) → \valid (b \cdot r)$. First, let's informally understand why this would make sense. Remember that in our proofs we're going to maintain that the ghost variable's value is always _valid_ according to $✓(a)$ from the RA. Also recall that while one thread might have $\own_γ(a)$, the ghost variable can have other parts in other threads (as we just saw in the problematic example). What a frame-preserving update says is, if a thread has $a$ and other threads own $r$, for any such $r$ where the composition is valid (and thus that is actually possible), then changing $a$ to $b$ retains validity of the whole ghost variable. This is what guarantees that changes don't invalidate any ownership in other threads, or the global ghost variable.

To use a frame-preserving update, we need to introduce the _update modality_ $\pvs P$ (pronounced "update P"). You've already seen this come up in Coq proofs as `|==>` and ignored it with `iModIntro`.

Whenever $a \mupd b$ (there is a frame preserving update from $a$ to $b$), what we formally get in the logic is an entailment $\own_γ(a) ⊢ \pvs \own_γ(b)$. The intuitive reading of the whole entailment is easier to start with than the update modality in isolation: it's possible to change ghost state so that if $\own_γ(a)$ was true before, afterward $\own_γ(b)$ is true. It's not the case that $\own_γ(a) ⊢ \own_γ(b)$; you should think of the update as actually changing (ghost) state, and $b$ isn't true previously. However, for practical purposes we'll see that while verifying a program $\pvs P$ can be turned into $P$.

The next API we need for ghost variables is to allocate them initially. The rule for this is fairly simple: $∀ a, \lift{✓(a)} ⊢ \pvs ∃ γ, \own_γ(a)$. This says that we can always change ghost state (that's the reading of the $\pvs$) to create a new variable with some name $γ$, and its initial value is any valid element $a$.

The model of the update modality (its definition in the model where iProp is $M \to \Prop$) is the following: $(\pvs P)(a) \triangleq ∃ b.\, a \mupd b ∧ P(b)$. That is, the current state/resources $a$ could be transformed into some thing else $b$ via a frame-preserving update to make $P$ true.

Let's look at some examples of ghost variables and their updates in Coq.

```coq
From sys_verif.program_proof Require Import prelude empty_ffi.
From Perennial.algebra Require Import ghost_var.
From Perennial.program_proof Require Import std_proof.
From Goose.sys_verif_code Require Import concurrent.

Section goose.
Context `{hG: !heapGS Σ}.
Context `{ghost_varG0: ghost_varG Σ Z}.
Open Scope Z_scope.

```

### Plain ghost variables

The first example we'll see is so-called "plain" ghost variables. These aren't quite so plain in that they have a value and a fraction, and the fraction can be split. This is just like our fracRA example.

The library hides the literal `own` construct in Iris behind some sealing machinery. Despite this, we can still print its definition with the following:

```coq
Print ghost_var.ghost_var_def.
```

:::: note Output

```txt title="coq output"
ghost_var.ghost_var_def =
λ (Σ : gFunctors) (A : Type) (ghost_varG0 : ghost_varG Σ A)
  (γ : gname) (dq : dfrac) (a : A), own γ (dfrac_agree.to_dfrac_agree dq a)
     : ∀ {Σ : gFunctors} {A : Type},
         ghost_varG Σ A → gname → dfrac → A → iProp Σ

Arguments ghost_var.ghost_var_def {Σ} {A}%type_scope {ghost_varG0} γ dq a
```

::::

The actual value passed to `own` uses `dfrac_agree.to_frac_agree`, which constructs an element of the dfrac_agree RA; that's the actual RA as defined in Iris.

---

```coq
Lemma ghost_var_change_ex1 γ :
  ghost_var γ (DfracOwn 1) 7%Z -∗ |==> ghost_var γ (DfracOwn 1) 23%Z.
Proof.
  iIntros "H".
  (* We use `iMod` to "execute" a ghost update. This is only legal because the
  goal allows it, which is true for a goal that starts with `|==>` (as we have
  here) or a WP goal. *)
  iMod (ghost_var_update 23%Z with "H") as "H".
  (* _After_ we're done doing ghost updates, we can remove the update modality
  from the goal with iModIntro. *)
  iModIntro.
  iExact "H".
Qed.

```

Here's a special case allocation lemma for this particular type of ghost state. (I'm using `@ghost_var_alloc Σ` rather than `ghost_var_alloc` to reduce some noise in the output.)

```coq
Check (@ghost_var_alloc Σ).
```

:::: note Output

```txt title="coq output"
@ghost_var_alloc Σ
     : ∀ (A : Type) (ghost_varG0 : ghost_varG Σ A) (a : A),
         ⊢ |==> ∃ γ : gname, ghost_var γ (DfracOwn 1) a
```

::::

### Discardable fractions

For our second example of an RA and its ghost variables, let's look at _discardable fractions_ (dfrac). You've seen `DfracOwn 1` instead of just the fraction 1; now we'll see (roughly) how that works.

Discardable fractions are like fractions between 0 and 1 (excluding 0, including 1), with the addition of a special $ε$ value, called `DfracDiscarded`. You can see a more complete description in the RA lecture's [discardable fractions section](./resource-algebra#discardable-fractions), or look at the definition of dfrac in Iris for actually all of the details:

```coq
Print dfrac_op_instance.
```

:::: note Output

```txt title="coq output"
dfrac_op_instance =
λ dq dp : dfrac,
  match dq with
  | DfracOwn q =>
      match dp with
      | DfracOwn q' => DfracOwn (q + q')
      | DfracDiscarded => DfracBoth q
      | DfracBoth q' => DfracBoth (q + q')
      end
  | DfracDiscarded =>
      match dp with
      | DfracDiscarded => DfracDiscarded
      | DfracOwn q' | DfracBoth q' => DfracBoth q'
      end
  | DfracBoth q =>
      match dp with
      | DfracDiscarded => DfracBoth q
      | DfracOwn q' | DfracBoth q' => DfracBoth (q + q')
      end
  end
     : Op dfrac
```

::::

Discardable fractions are used in the ghost variable API: instead of composing fractions with $q_1 + q_2$, we're actually using $dq_1 : \mathrm{dfrac}$ and composing with dfrac composition $dq_1 \cdot dq_2$ (which does still behave a lot like addition).

For this discussion there are two salient aspects of dfrac composition:

- $∀ dq, ✓(dq) → dq \mupd ε$. This means that it is valid to change any fraction to the value $ε$.
- $∀ (dq: \mathrm{dfrac}), ε \cdot ε = ε$. This makes owning a discarded $ε$ duplicable (in fact, ownership is also persistent).

The first is the "discard" part of discardable fractions, and it means we have the following ghost update:

```coq
Check (@ghost_var_persist Σ).
```

:::: note Output

```txt title="coq output"
@ghost_var_persist Σ
     : ∀ (A : Type) (ghost_varG0 : ghost_varG Σ A)
         (γ : gname) (q : Qp) (a : A),
         ghost_var γ (DfracOwn q) a ==∗ ghost_var γ DfracDiscarded a
```

::::

The second property about persistence is what makes discardable fractions especially useful:

```coq
Check (@ghost_var_persistent Σ).
```

:::: note Output

```txt title="coq output"
@ghost_var_persistent Σ
     : ∀ (A : Type) (ghost_varG0 : ghost_varG Σ A) (γ : gname) (a : A),
         Persistent (ghost_var γ DfracDiscarded a)
```

::::

### Proof of the example

Let's put this together to verify the parallel add example. We'll use an existing spec for the Spawn/JoinHandle API, lock invariants, and two ghost variables.

The essence of the proof is really in the lock invariant. `l` here is the address of the `x` variable in the Go code.

The idea is that the two variables correspond to the component each thread has added to the shared variable. the lock owns half of each variable; the first thread has the other half of `γ1` and the second thread has the other half of `γ2`.

The lock invariant also connects all of this ghost state back to the physical state: the value stored in `l` is the sum of the two ghost variables.

We also maintain that both ghost variables are less than 2 so that we can prove the additions don't overflow.

```coq
Definition lock_inv γ1 γ2 l : iProp _ :=
  ∃ (x: w64) (x1 x2: Z),
    "Hx1" :: ghost_var γ1 (DfracOwn (1/2)) x1 ∗
    "Hx2" :: ghost_var γ2 (DfracOwn (1/2)) x2 ∗
    "x" ∷ l ↦[uint64T] #x ∗
    "%Hsum" ∷ ⌜x1 ≤ 2 ∧ x2 ≤ 2 ∧ uint.Z x = (x1 + x2)%Z⌝.

Lemma wp_ParallelAdd3 :
  {{{ True }}}
    ParallelAdd3 #()
  {{{ (x: w64), RET #x; ⌜uint.Z x = 4⌝ }}}.
Proof using All.
  wp_start as "_".
  iMod (ghost_var_alloc 0) as (γ1) "[Hv1_1 Hx1_2]".
  iMod (ghost_var_alloc 0) as (γ2) "[Hv2_1 Hx2_2]".


```

This proof illustrates one more thing, incidentally. The code creates a mutex before the variable `x` that it protects. This turns out not to be an issue; the Goose mutex specifications support this use case. What we do is first create a "free lock", which is a lock without a lock invariant (yet).

```coq
  wp_apply wp_new_free_lock; iIntros (mu_l) "Hlock".
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  ghost_varG0 : ghost_varG Σ Z
  Φ : val → iPropI Σ
  γ1, γ2 : gname
  mu_l : loc
  ============================
  "HΦ" : ∀ x : w64, ⌜uint.Z x = 4⌝ -∗ Φ #x
  "Hv1_1" : ghost_var γ1 (DfracOwn (1 / 2)) 0
  "Hx1_2" : ghost_var γ1 (DfracOwn (1 / 2)) 0
  "Hv2_1" : ghost_var γ2 (DfracOwn (1 / 2)) 0
  "Hx2_2" : ghost_var γ2 (DfracOwn (1 / 2)) 0
  "Hlock" : is_free_lock mu_l
  --------------------------------------∗
  WP let: "m" := #mu_l in
     let: "i" := ref_to uint64T #(W64 0) in
     let: "h1" := std.Spawn
                    (λ: <>,
                       Mutex__Lock "m";;
                       "i" <-[uint64T] ![uint64T] "i" + #(W64 2);;
                       Mutex__Unlock "m";; #()) in
     let: "h2" := std.Spawn
                    (λ: <>,
                       Mutex__Lock "m";;
                       "i" <-[uint64T] ![uint64T] "i" + #(W64 2);;
                       Mutex__Unlock "m";; #()) in
     std.JoinHandle__Join "h1";;
     std.JoinHandle__Join "h2";;
     Mutex__Lock "m";; let: "y" := ![uint64T] "i" in Mutex__Unlock "m";; "y"
  {{ v, Φ v }}
```

::::

```coq
  wp_alloc x_l as "x".
  iMod (alloc_lock nroot _ _ (lock_inv γ1 γ2 x_l)
         with "Hlock [$x $Hv1_1 $Hv2_1]") as "#Hlock".
  { iPureIntro. done. }
  wp_pures.
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  ghost_varG0 : ghost_varG Σ Z
  Φ : val → iPropI Σ
  γ1, γ2 : gname
  mu_l, x_l : loc
  ============================
  "Hlock" : is_lock nroot #mu_l (lock_inv γ1 γ2 x_l)
  --------------------------------------□
  "HΦ" : ∀ x : w64, ⌜uint.Z x = 4⌝ -∗ Φ #x
  "Hx1_2" : ghost_var γ1 (DfracOwn (1 / 2)) 0
  "Hx2_2" : ghost_var γ2 (DfracOwn (1 / 2)) 0
  --------------------------------------∗
  WP let: "h1" := std.Spawn
                    (λ: <>,
                       Mutex__Lock #mu_l;;
                       #x_l <-[uint64T] ![uint64T] #x_l + #(W64 2);;
                       Mutex__Unlock #mu_l;; #())%V in
     let: "h2" := std.Spawn
                    (λ: <>,
                       Mutex__Lock #mu_l;;
                       #x_l <-[uint64T] ![uint64T] #x_l + #(W64 2);;
                       Mutex__Unlock #mu_l;; #()) in
     std.JoinHandle__Join "h1";;
     std.JoinHandle__Join "h2";;
     Mutex__Lock #mu_l;;
     let: "y" := ![uint64T] #x_l in Mutex__Unlock #mu_l;; "y"
  {{ v, Φ v }}
```

::::

Observe here that the `alloc_lock` above has consumed the `is_free_lock` and associated it with a chosen lock invariant. Importantly, we couldn't actually use the `wp_Mutex__Lock` specification before using `alloc_lock`.

```coq
  wp_apply (std_proof.wp_Spawn (ghost_var γ1 (DfracOwn (1/2)) 2) with "[Hx1_2]").
  {
    clear Φ.
    iIntros (Φ) "HΦ".
    wp_pures.
    wp_apply (wp_Mutex__Lock with "[$Hlock]"). iIntros "[locked Hinv]". iNamed "Hinv".
    wp_load.
    wp_store.
    iDestruct (ghost_var_agree with "Hx1_2 Hx1") as %Heq; subst.
    iMod (ghost_var_update_2 2 with "Hx1_2 Hx1") as "[Hx1_2 Hx1]".
    { rewrite dfrac_op_own Qp.half_half //. }
    wp_apply (wp_Mutex__Unlock with "[-HΦ Hx1_2 $Hlock $locked]").
    { iFrame.
      iPureIntro. split_and!; try word. }
    wp_pures.
    iApply "HΦ". iFrame. done.
  }
  iIntros (h_1) "h1".
  wp_apply (std_proof.wp_Spawn (ghost_var γ2 (DfracOwn (1/2)) 2) with "[Hx2_2]").
  {
    clear Φ.
    iIntros (Φ) "HΦ".
    wp_pures.
    wp_apply (wp_Mutex__Lock with "[$Hlock]"). iIntros "[locked Hinv]". iNamed "Hinv".
    wp_load.
    wp_store.
    iDestruct (ghost_var_agree with "Hx2_2 Hx2") as %Heq; subst.
    iMod (ghost_var_update_2 2 with "Hx2_2 Hx2") as "[Hx2_2 Hx2]".
    { rewrite dfrac_op_own Qp.half_half //. }
    wp_apply (wp_Mutex__Unlock with "[-HΦ Hx2_2 $Hlock $locked]").
    { iFrame.
      iPureIntro. split_and!; try word. }
    wp_pures.
    iApply "HΦ". iFrame. done.
  }
  iIntros (h_2) "h2".
  wp_pures.
  wp_apply (wp_JoinHandle__Join with "[$h1]"). iIntros "Hx1_2".
  wp_apply (wp_JoinHandle__Join with "[$h2]"). iIntros "Hx2_2".
  wp_apply (wp_Mutex__Lock with "[$Hlock]"). iIntros "[locked Hinv]". iNamed "Hinv".
  iDestruct (ghost_var_agree with "Hx1_2 Hx1") as %Heq; subst.
  iDestruct (ghost_var_agree with "Hx2_2 Hx2") as %Heq; subst.
  wp_load.
  wp_apply (wp_Mutex__Unlock with "[$locked $Hlock Hx1 Hx2 x]").
  { iFrame. iPureIntro. split_and!; word. }
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iPureIntro. word.
Qed.

End goose.
```
