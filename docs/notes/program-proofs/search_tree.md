---
# Auto-generated from literate source. DO NOT EDIT.
category: demo
tags: literate
order: -1
pageInfo: ["Date", "Category", "Tag"]
---

# Demo: binary search tree

A binary search tree is a data structure for fast lookup, addition, and removal of items based on sorted keys. The key idea is an invariant that the key of every node is greater than all keys in that node's left subtree, and less than the keys in the right subtree.

We will verify a simple implementation of a binary search tree which only stores integer keys, with no associated values, and with no delete operation (though you may want to add one as a fun exercise).

The full Go source is at [go/heap/search_tree.go](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/go/heap/search_tree.go) in the exercises repo for the class.

This is the Go data structure for a single node of the tree:

```go
type SearchTree struct {
	key   uint64
	left  *SearchTree
	right *SearchTree
}
```

For the proof, first we'll set up the representation invariant `own_tree` for a `SearchTree`, relating it to the `gset w64` of elements it logically contains.

Then, we'll prove specifications based on this representation invariant.

---

```rocq
From sys_verif.program_proof Require Import prelude empty_ffi.
From sys_verif.program_proof Require Import heap_init.

Section proof.
Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.


```

`tree_root` is the core definition of a (non-empty) tree rooted at some key.

See `own_tree_F` for the context of how this is used.

```rocq
Definition tree_root (own_tree: loc -d> gset w64 -d> iPropO Σ)
  (l: loc) (keys: gset w64) : iPropO Σ :=
  (∃ (key: w64) (left_l right_l: loc) (l_keys r_keys: gset w64),
   "key" :: l ↦s[heap.SearchTree :: "key"] key ∗
   "left" :: l ↦s[heap.SearchTree :: "left"] left_l ∗
   "right" :: l ↦s[heap.SearchTree :: "right"] right_l ∗
   (* the pointers in a tree themselves point to subtrees *)
   "Hleft" :: ▷ own_tree left_l l_keys ∗
   "Hright" :: ▷ own_tree right_l r_keys ∗
   (* the elements of the whole tree combine the root node and the subtrees *)
   "%Hkeys" :: ⌜keys = {[key]} ∪ l_keys ∪ r_keys⌝ ∗
   (* the core binary search tree invariant: the elements in the subtree are
   less than the root, and the root is less than the elements in the right
   subtree *)
   "%Hleft_bound" :: ⌜∀ (k: w64), k ∈ l_keys → uint.Z k < uint.Z key⌝ ∗
   "%Hright_bound" :: ⌜∀ (k: w64), k ∈ r_keys → uint.Z key < uint.Z k⌝
  )%I.

```

The representation of a tree relates a `loc` for the root pointer (to a `SearchTree` struct) to a set of elements of type `gset w64`. The desired definition is recursive, since a tree contains pointers to other trees in turn.

This is using an Iris mechanism to write recursive definitions. We won't go into the details here, but you do need to be able to read the definition `own_tree_F`. Notice that `own_tree_F` takes a predicate `own_tree` as an argument. What `own_tree_unfold` proves is that `own_tree` is equal to `own_tree_F` applied to the original `own_tree` - this is what's called a "fixpoint" of `own_tree_F` because `own_tree_F own_tree = own_tree`.

```rocq
Definition own_tree_F (own_tree: loc -d> gset w64 -d> iPropO Σ) :
  loc -d> gset w64 -d> iPropO Σ :=
  (λ l keys,
  ("%Hnull" :: ⌜l = null⌝ ∗ ⌜keys = ∅⌝) ∨
  "%Hnon_null" :: ⌜l ≠ null⌝ ∗ tree_root own_tree l keys)%I.

#[local] Instance own_tree_F_contractive : Contractive own_tree_F.
Proof.
  rewrite /own_tree_F /tree_root.
  solve_contractive.
Qed.

Definition own_tree : loc → gset w64 → iProp Σ := fixpoint own_tree_F.

Lemma own_tree_unfold l keys :
  own_tree l keys ⊣⊢ own_tree_F (own_tree) l keys.
Proof. apply (fixpoint_unfold own_tree_F). Qed.

Lemma own_tree_null keys :
  own_tree null keys ⊣⊢ ⌜keys = ∅⌝.
Proof.
  rewrite own_tree_unfold /own_tree_F.
  rewrite /named.
  iSplit.
  - iIntros "[[% %] | [% _]]".
    + auto.
    + contradiction.
  - iIntros "%"; subst. auto.
Qed.

Lemma own_tree_non_null l keys :
  l ≠ null →
  own_tree l keys ⊣⊢ tree_root own_tree l keys.
Proof.
  iIntros (Hnon_null).
  rewrite own_tree_unfold /own_tree_F.
  iSplit.
  - iIntros "[[% %]| [% $]]".
    contradiction.
  - iIntros "H". iRight. iFrame "%∗".
Qed.

```

Go source:

```go
func NewSearchTree() *SearchTree {
	// NOTE: this pattern works around a Goose bug with translating the nil
	// constant
	var s *SearchTree
	return s
}
```

```rocq
Lemma wp_NewSearchTree :
  {{{ is_pkg_init heap.heap }}}
    @! heap.heap.NewSearchTree #()
  {{{ (l: loc), RET #l; own_tree l ∅ }}}.
Proof.
  wp_start as "_".
  wp_auto.
  iApply "HΦ".
  iApply own_tree_null; done.
Qed.

```

Go source:

```go
func (t *SearchTree) Contains(key uint64) bool {
	if t == nil {
		return false
	}
	if key == t.key {
		return true
	}
	if key < t.key {
		return t.left.Contains(key)
	}
	return t.right.Contains(key)
}
```

```rocq
Lemma wp_SearchTree__Contains (needle: w64) l keys :
  {{{ is_pkg_init heap.heap ∗ own_tree l keys }}}
    l @ (ptrTⁱᵈ heap.SearchTreeⁱᵈ) @ "Contains" #needle
  {{{ RET #(bool_decide (needle ∈ keys)); own_tree l keys }}}.
Proof.

```

`Contains` is recursive. We'll use Löb induction to prove it correct.

Löb induction says `∀ P, (▷ P → P) → P`. This seems pretty magical: we can assume [▷P] when proving any proposition P! The reason this is sound is because of how the [▷] modality prevents us from using [▷P] immediately and not doing any work. In a program proof, the effect of Löb induction is that we can assume the correctness of the function we're proving after it has taken _at least one step_. This means that the spec can be used as an induction hypothesis for all recursive calls, but not for the original call (which would be unsound).

Note that we can't use this mechanism to prove a program's recursion eventually terminates, so it only works to prove properties about a function if it terminates.

```rocq
  iLöb as "IH" forall (l keys).
  wp_start as "Htree". wp_auto.
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  globalsGS0 : globalsGS Σ
  go_ctx : GoContext
  needle : w64
  l : loc
  keys : gset w64
  Φ : val → iPropI Σ
  t_ptr, key_ptr : loc
  ============================
  "IH" : ∀ (l0 : loc) (keys0 : gset w64) (x : val → iPropI Σ),
           is_pkg_init heap ∗ own_tree l0 keys0 -∗
           ▷ (own_tree l0 keys0 -∗ x (# (bool_decide (needle ∈ keys0)))) -∗
           WP # (method_callv (ptrTⁱᵈ heap.SearchTreeⁱᵈ) "Contains" (# l0))
                (# needle)
           {{ v, x v }}
  _ : is_pkg_init heap
  --------------------------------------□
  "Htree" : own_tree l keys
  "HΦ" : own_tree l keys -∗ Φ (# (bool_decide (needle ∈ keys)))
  "t" : t_ptr ↦ l
  "key" : key_ptr ↦ needle
  --------------------------------------∗
  WP exception_do
       ((if: # (bool_decide (l = null)) then return: # false else do: # ()) ;;;
        (if: ![# uint64T] (# key_ptr) =
             ![# uint64T] (struct.field_ref (# heap.SearchTree)
                             (# "key"%go) ![# ptrT]
                             (# t_ptr))
         then return: # true else do: # ()) ;;;
        (if: ![# uint64T] (struct.field_ref (# heap.SearchTree)
                             (# "key"%go) ![# ptrT]
                             (# t_ptr)) >
             ![# uint64T] (# key_ptr)
         then return: (let: "$a0" := ![# uint64T] (# key_ptr) in
                       method_call (# (ptrTⁱᵈ heap.SearchTreeⁱᵈ))
                         (# "Contains"%go)
                         ![# ptrT] (struct.field_ref
                                      (# heap.SearchTree)
                                      (# "left"%go) ![
                                      # ptrT] (# t_ptr))
                         "$a0")
         else do: # ()) ;;;
        return: (let: "$a0" := ![# uint64T] (# key_ptr) in
                 method_call (# (ptrTⁱᵈ heap.SearchTreeⁱᵈ))
                   (# "Contains"%go)
                   ![# ptrT] (struct.field_ref (# heap.SearchTree)
                                (# "right"%go) ![# ptrT]
                                (# t_ptr))
                   "$a0"))
  {{ v, Φ v }}
```

::::

Notice that the ▷ in front of "IH" has disappeared because we've taken a step. We're now free to use it whenever there's a call to `SearchTree__Contains`.

```rocq
  wp_if_destruct; try wp_auto.
  { (* If the root is nil, then the tree is empty. We need to prove that to show
       that returning false is the right thing to do. *)
    (* we need to prove this before `iApply HΦ` since the proof requires
    "Htree" *)
    iAssert (⌜needle ∉ keys⌝)%I as %Hnotin.
    { iDestruct (own_tree_null with "Htree") as %Hkeys; subst.
      iPureIntro; set_solver. }
    rewrite bool_decide_eq_false_2; [ done | ].
    iApply "HΦ". iFrame. }

  (* non-nil cases *)
  assert (l ≠ null) as Hnon_null by congruence.
  iDestruct (own_tree_non_null with "Htree") as "Htree"; [ done | ].
  iRename "key" into "key_var".
  iNamed "Htree". subst keys.
  wp_auto.
  wp_if_destruct.
  { (* found needle at root *)
    rewrite bool_decide_eq_true_2.
    { set_solver. }
    iApply "HΦ".
    iApply own_tree_non_null; auto.
    iFrame "key left right Hleft Hright %".
    iPureIntro; set_solver.
  }

  (* else: didn't find at root *)
  assert (needle ≠ key) as Hnotkey by congruence.
  wp_auto.
  wp_if_destruct; try wp_auto.
  - (* recursive subcall, to the left tree *)
    wp_apply ("IH" with "[$Hleft]").
    iIntros "Hleft".
    iDestruct ("HΦ" with "[key left right Hleft Hright]") as "HΦ".
    { iApply own_tree_non_null; auto.
      iFrame "left right ∗%".
      done.
    }
    (* We need to prove that searching on the left is equivalent to searching in
    the whole tree. Intuitively, this is true because `needle ≠ key` and the
    binary search invariant guarantees that `needle` won't be found on the
    right. *)
    wp_auto.
    iExactEq "HΦ".
    repeat f_equal.
    apply bool_decide_ext.
    (* this is true because of the search invariant, not simple set reasoning *)
    assert (needle ∉ r_keys).
    { intros Hin. apply Hright_bound in Hin. lia. }
    (* [set_solver] can automate the remainder of the proof *)
    set_solver.
  - (* recursive subcall, to the right tree (essentially identical proof to the
    left tree) *)
    wp_apply ("IH" with "[$Hright]").
    iIntros "Hright".
    iDestruct ("HΦ" with "[key left right Hleft Hright]") as "HΦ".
    { iApply own_tree_non_null; auto.
      iFrame "left right ∗%".
      done.
    }
    wp_auto.
    iExactEq "HΦ".
    repeat f_equal.
    apply bool_decide_ext.
    (* [set_solver] can actually use [lia] as a helper tactic and do this whole
    proof automatically *)
    set_solver by lia.
Qed.

```

Go source:

```go
func singletonTree(key uint64) *SearchTree {
	// NOTE: same workaround for Goose bug
	var s *SearchTree
	return &SearchTree{key: key, left: s, right: s}
}
```

```rocq
Lemma wp_singletonTree (key: w64) :
  {{{ is_pkg_init heap.heap }}}
    @! heap.heap.singletonTree #key
  {{{ (l: loc), RET #l; own_tree l {[key]} }}}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_alloc t_l as "Hl".
  iDestruct (pointsto_not_null with "Hl") as %Hnot_null.
  { reflexivity. }
  iApply struct_fields_split in "Hl". iNamed "Hl".
  cbn [heap.SearchTree.key' heap.SearchTree.left' heap.SearchTree.right'].
  wp_auto.
  iApply "HΦ".
  rewrite own_tree_unfold /own_tree_F.
  iRight.
  iSplit; [ done | ].
  iFrame "Hkey Hleft Hright".
  iExists ∅, ∅. iFrame.
  rewrite own_tree_null.
  iPureIntro.
  split_and!; auto.
  - set_solver.
  - set_solver.
  - set_solver.
Qed.

```

Go source:

```go
func (t *SearchTree) Insert(key uint64) *SearchTree {
	if t == nil {
		return singletonTree(key)
	}
	// modify in-place
	if key < t.key {
		t.left = t.left.Insert(key)
	} else if t.key < key {
		t.right = t.right.Insert(key)
	}
	// if t.Key == key then key is already present
	return t
}
```

```rocq
Lemma wp_SearchTree__Insert (new_key: w64) l keys :
  {{{ is_pkg_init heap.heap ∗ own_tree l keys }}}
    l @ (ptrTⁱᵈ heap.SearchTreeⁱᵈ) @ "Insert" #new_key
  {{{ (l': loc), RET #l'; own_tree l' (keys ∪ {[new_key]}) }}}.
Proof.
  iLöb as "IH" forall (l keys).
  wp_start as "Htree".
  wp_auto.
  wp_if_destruct; try wp_auto.
  { wp_apply wp_singletonTree.
    iDestruct (own_tree_null with "Htree") as %Hkeys; subst. iClear "Htree".
    iIntros (l') "Htree".
    wp_auto.
    iApply "HΦ".
    iExactEq "Htree".
    f_equal. set_solver. }

  assert (l ≠ null) as Hnot_null by congruence.
  iDestruct (own_tree_non_null with "Htree") as "Htree"; [ auto | ].
  iRename "key" into "key_var".
  iNamed "Htree". subst keys.
  wp_auto.
  wp_if_destruct; try wp_auto.
  { wp_apply ("IH" with "[$Hleft]").
    iIntros (left_l') "Hleft".
    wp_auto.
    iApply "HΦ".
    iApply own_tree_non_null; [ done | ].
    (* need to re-prove binay search invariant *)
    iFrame "key left right Hleft Hright %".
    iPureIntro.
    split_and!; auto.
    - set_solver.
    - set_solver.
  }
  wp_if_destruct; try wp_auto.
  { wp_apply ("IH" with "[$Hright]").
    iIntros (right_l') "Hright".
    wp_auto.
    iApply "HΦ".
    iApply own_tree_non_null; [ done | ].
    iFrame "key left right Hleft Hright %".
    iPureIntro.
    split_and!.
    - set_solver.
    - set_solver.
  }
  (* key was already present *)
  assert (key = new_key) by word; subst new_key.
  iApply "HΦ".
  iApply own_tree_non_null; [ auto | ].
  iFrame "key left right Hleft Hright %".
  iPureIntro.
  (* there's only one goal because the left and right subtrees are unchanged, so
  the search invariant is proven automatically *)
  set_solver. (* this is where we prove that even though we don't modify the
    search tree, it's the same as doing ∪ {[key]} *)
Qed.

```

```rocq
End proof.
```
