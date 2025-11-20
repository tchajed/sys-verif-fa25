---
# Auto-generated from literate source. DO NOT EDIT.
category: assignment
tags: literate
dir:
  order: 5
icon: file-lines
shortTitle: "Sharded hashmap"
---

# Assignment 4: concurrent sharded hash map

In this assignment, you'll finish the proof of a concurrent, sharded hash map. You'll only be doing proofs: all theorem statements and invariants are provided.

You should start by reading and understanding the [code](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/go/sharded_hashmap/sharded_hashmap.go). Really! Go read it! And spend some time figure out why you think it works and how you would explain its correctness without any of the tools in this proof. **Exercise:** Write this down in a Rocq comment in your solution. _(10 points)_

I suggest you do a quick skim over everything to understand the ideas and intuition, especially compared to just blindly trying to fill in proofs. The sub-sections should also be fairly independent so feel free to skip around to avoid getting stuck for too long on one part; it's better you attempt every part than finish some proofs and never start the others.

A secondary goal is for you to _understand_ this proof, so keep that in the back of your mind - there is another writing exercise at the end of this file.

```rocq
From sys_verif.program_proof Require Import prelude empty_ffi.
From iris.algebra Require Import ofe auth excl gmap.
From New.proof Require Import sync.
From New.generatedproof.sys_verif_code Require Import sharded_hashmap.
From Perennial.algebra Require Import ghost_var.

Open Scope Z_scope.
Add Printing Coercion Z.of_nat.

(* expand `set_solver` a bit (TODO: this should be upstreamed into std++) *)
Section set_solver_auto.
  #[global] Instance set_unfold_map_disjoint K `{Countable K} A (m1 m2: gmap K A) Q {Hunfold: SetUnfold (dom m1 ## dom m2) Q} :
    SetUnfold (m1 ##ₘ m2) Q.
  Proof.
    constructor.
    rewrite map_disjoint_dom.
    destruct Hunfold as [Hunfold]. rewrite Hunfold //.
  Qed.

  #[global] Instance set_unfold_seqZ x n m :
    SetUnfoldElemOf x (seqZ n m) (n ≤ x < n + m).
  Proof.
    constructor.
    rewrite elem_of_seqZ //.
  Qed.
End set_solver_auto.

```

## auth_map resource algebra

The ghost state for this proof uses an auth map RA. The definition of the RA uses constructions from Iris (hence there is no definition of composition or validity here). What this library does is wraps up this RA in nice definitions, hiding the direct `own` predicates from the user.

```rocq
Module auth_map.


```

A good deal of boilerplate is needed to create a resource algebra. The interesting parts are just `auth_mapR` (this is the algebraic structure, defined using existing structures), `auth_map_auth_def`, and `auth_map_frag_def`.

```rocq
  Definition auth_mapR K `{Countable K} A : ucmra :=
    authUR (gmapUR K (exclR (leibnizO A))).

  Class auth_mapG Σ (K: Type) `{Countable K} (A: Type) :=
    AuthMapG {
        #[global] auth_map_inG :: inG Σ (auth_mapR K A);
    }.
  Global Hint Mode auth_mapG - ! - - - : typeclass_instances.

  Definition auth_mapΣ K `{Countable K} A : gFunctors :=
    #[ GFunctor (auth_mapR K A) ].

  #[global] Instance subG_auth_mapG Σ K `{Countable K} A :
    subG (auth_mapΣ K A) Σ → auth_mapG Σ K A.
  Proof. solve_inG. Qed.

  Local Definition auth_map_auth_def `{auth_mapG Σ K A}
      (γ : gname) (m: gmap K A) : iProp Σ :=
    own γ (● ((Excl <$> m): gmapUR K (exclR (leibnizO A)))).
  Local Definition auth_map_auth_aux : seal (@auth_map_auth_def). Proof. by eexists. Qed.
  Definition auth_map_auth := auth_map_auth_aux.(unseal).
  Local Definition auth_map_auth_unseal :
    @auth_map_auth = @auth_map_auth_def := auth_map_auth_aux.(seal_eq).
  Global Arguments auth_map_auth {Σ K _ _ A _} γ m.

  (* Unlike most uses of authUR (gmapUR ...), the fragments here are going to be
  arbitrary sub-maps, not typically singleton maps (e.g., the definition
  of `l ↦ v`). *)
  Local Definition auth_map_frag_def `{auth_mapG Σ K A}
      (γ : gname) (m: gmap K A) : iProp Σ :=
    own γ (auth_frag ((Excl <$> m): gmapUR K (exclR (leibnizO A)))).
  Local Definition auth_map_frag_aux : seal (@auth_map_frag_def). Proof. by eexists. Qed.
  Definition auth_map_frag := auth_map_frag_aux.(unseal).
  Local Definition auth_map_frag_unseal :
    @auth_map_frag = @auth_map_frag_def := auth_map_frag_aux.(seal_eq).
  Global Arguments auth_map_frag {Σ K _ _ A _} γ m.

  Local Ltac unseal := rewrite ?auth_map_auth_unseal ?auth_map_frag_unseal /auth_map_auth_def /auth_map_frag_def.

  #[local] Lemma lookup_included_2 {K} `{Countable K} {A: cmra} (m1 m2: gmap K A) (i: K) :
    m1 ≼ m2 →
    m1 !! i ≼ m2 !! i.
  Proof.
    intros.
    apply lookup_included; auto.
  Qed.

  Section lemmas.
  Context `{auth_mapG Σ K A}.

  Implicit Types (m: gmap K A) (a: A).

  #[global] Instance auth_map_auth_timeless γ m :
    Timeless (auth_map_auth γ m).
  Proof. unseal. apply _. Qed.
  #[global] Instance auth_map_frag_timeless γ m :
    Timeless (auth_map_frag γ m).
  Proof. unseal. apply _. Qed.


```

Each instance of this RA consists of two types of predicates: `auth_map_auth γ m` and `auth_map_frag γ m`. In both cases `m` is an arbitrary `gmap K A`.

The definition of auth_map serves to make all of the lemmas below true. You can take this as the API for this construction, and can ignore the rest as an implementation detail (certainly that's what you would do if only using this library as opposed to implementing it).

The basic idea is that there is only one `auth_map_auth γ m`, controlling some "*auth*oritative" or "central" map `m`, but many *frag*ments `auth_map γ m'`. It's always the case that `auth_map_frag γ m ∗ auth_map_frag γ m' ⊢ ⌜m' ⊆ m⌝`, and `auth_map_frag γ (m ∪ m')` separates when `m` and `m'` are disjoint.

There are no proofs for you to do in this section. These proofs are fairly technical and you can often do a proof by composing existing ghost state libraries, rather than writing your own. (Even this library was probably not necessary in retrospect.)

```rocq
  Lemma auth_map_init :
    ⊢ |==> ∃ γ, auth_map_auth γ (∅: gmap K A).
  Proof.
    unseal.
    iApply (own_alloc (● (∅ : gmap K (exclR (leibnizO A))))).
    apply auth_auth_valid. done.
  Qed.

  (* The symbol `##ₘ` is `map_disjoint`. The theorem `map_disjoint_dom` shows `m1 ##ₘ m2 ↔ dom m1 ## dom m2`, and in practice working with the domains is easier because `set_solver` can automate many proofs. *)
  Lemma auth_map_frag_disjoint γ m1 m2 :
    auth_map_frag γ m1 -∗ auth_map_frag γ m2 -∗ ⌜m1 ##ₘ m2⌝.
  Proof.
    unseal. iIntros "Hauth Hfrag".
    iDestruct (own_valid_2 with "Hauth Hfrag") as %Hunion.
    iPureIntro.
    apply auth_frag_op_valid_1 in Hunion.
    apply gmap_op_valid_disjoint in Hunion.
    { set_solver. }
    intros k x Hget1.
    fmap_Some in Hget1 as x'.
    apply _.
  Qed.

  Lemma auth_map_frag_combine γ m1 m2 :
    auth_map_frag γ m1 ∗ auth_map_frag γ m2 -∗ auth_map_frag γ (m1 ∪ m2).
  Proof.
    iIntros "[Hauth Hfrag]".
    iDestruct (auth_map_frag_disjoint with "Hauth Hfrag") as %Hdisjoint.
    unseal.
    iStopProof.
    rewrite -own_op.
    rewrite -auth_frag_op.
    rewrite gmap_op_union.
    { apply map_disjoint_fmap; auto. }
    rewrite map_fmap_union //.
  Qed.

  Lemma auth_map_frag_split γ m1 m2 :
    m1 ##ₘ m2 →
    auth_map_frag γ (m1 ∪ m2) -∗
    auth_map_frag γ m1 ∗ auth_map_frag γ m2.
  Proof.
    intros Hdisj.
    unseal.
    rewrite -own_op.
    rewrite -auth_frag_op.
    rewrite gmap_op_union.
    { apply map_disjoint_fmap; auto. }
    rewrite map_fmap_union. iIntros "$".
  Qed.

  Lemma auth_map_frag_subset γ m m' :
    auth_map_auth γ m -∗ auth_map_frag γ m' -∗ ⌜m' ⊆ m⌝.
  Proof.
    unseal. iIntros "Hauth Hfrag".
    iDestruct (own_valid_2 with "Hauth Hfrag") as %Hin.
    iPureIntro.
    apply auth_both_valid_discrete in Hin as [Hin _].
    apply map_subseteq_spec.
    intros i x Hgetm'.
    apply (lookup_included_2 _ _ i) in Hin.
    rewrite !lookup_fmap Hgetm' /= in Hin.
    destruct (m !! i) eqn:Hgetm.
    { rewrite /= in Hin.
      apply @Excl_included in Hin.
      congruence. }
    apply Some_included_is_Some in Hin.
    rewrite /= in Hin. destruct Hin; congruence.
  Qed.

  Lemma auth_map_alloc1 k v γ m :
    k ∉ dom m →
    auth_map_auth γ m ==∗
    auth_map_auth γ (<[k := v]> m) ∗ auth_map_frag γ {[k := v]}.
  Proof.
    unseal. iIntros (Hdisj) "Hauth".
    rewrite -own_op.
    iApply (own_update with "Hauth").
    apply auth_update_alloc.
    rewrite !fmap_insert.
    apply @gmap.alloc_local_update; [ | done ].
    apply not_elem_of_dom.
    set_solver.
  Qed.

  Lemma auth_map_alloc_empty γ m :
    (* these are actually equal, so we don't even need an update modality *)
    auth_map_auth γ m -∗
    auth_map_auth γ m ∗ auth_map_frag γ (∅: gmap K A).
  Proof.
    unseal.
    rewrite -own_op.
    iIntros "H". iExact "H".
  Qed.

  Lemma auth_map_insert k v γ m v0 :
    auth_map_auth γ m ∗ auth_map_frag γ {[k := v0]} ==∗
    auth_map_auth γ (<[k := v]> m) ∗ auth_map_frag γ {[k := v]}.
  Proof.
    iIntros "[Hauth Hfrag]".
    iDestruct (auth_map_frag_subset with "Hauth Hfrag") as %Hsub.
    apply map_singleton_subseteq_l in Hsub.
    unseal.
    iCombine "Hauth Hfrag" as "H".
    rewrite -own_op.
    iApply (own_update with "H").
    apply auth_update.
    rewrite !fmap_insert !fmap_empty !insert_empty.
    apply @gmap.singleton_local_update_any.
    intros x Hget.
    fmap_Some in Hget.
    apply exclusive_local_update; done.
  Qed.

  Lemma auth_map_insert_map k v γ m sub_m :
    k ∈ dom sub_m →
    auth_map_auth γ m ∗ auth_map_frag γ sub_m ==∗
    auth_map_auth γ (<[k := v]> m) ∗ auth_map_frag γ (<[k := v]> sub_m).
  Proof.
    iIntros (Hdom) "[Hauth Hfrag]".
    apply elem_of_dom in Hdom as [v0 Hget].
    assert (sub_m = {[k:=v0]} ∪ delete k sub_m) as Hsplit.
    {
      rewrite -insert_union_singleton_l.
      rewrite insert_delete_eq.
      rewrite insert_id //.
    }
    rewrite Hsplit.
    iDestruct (auth_map_frag_split with "Hfrag") as "[Hk Hfrag]".
    { set_solver. }
    iMod (auth_map_insert k v with "[$Hauth $Hk]") as "[$ Hk]".
    iModIntro.
    iDestruct (auth_map_frag_combine with "[$Hk $Hfrag]") as "Hfrag".
    iExactEq "Hfrag". f_equal.
    rewrite -!insert_union_singleton_l.
    rewrite insert_insert_eq.
    done.
  Qed.

  Lemma auth_map_insert_map_new k v γ m sub_m :
    k ∉ dom m →
    auth_map_auth γ m ∗ auth_map_frag γ sub_m ==∗
    auth_map_auth γ (<[k := v]> m) ∗ auth_map_frag γ (<[k := v]> sub_m).
  Proof.
    iIntros (Hnot_in) "[Hauth Hfrag]".
    iMod (auth_map_alloc1 k v with "Hauth") as "[$ Hk]".
    { auto. }
    iModIntro.
    iDestruct (auth_map_frag_combine with "[$Hk $Hfrag]") as "Hfrag".
    iExactEq "Hfrag". f_equal.
    rewrite -insert_union_singleton_l //.
  Qed.

End lemmas.

End auth_map.

Section proof.
Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.
Context `{hG1: !auth_map.auth_mapG Σ w32 w64}.
Context `{hG2: !auth_map.auth_mapG Σ Z (gset w32)}.
Context `{hG3: !ghost_varG Σ (gmap w32 w64)}.

#[global] Instance : IsPkgInit sharded_hashmap := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf sharded_hashmap := build_get_is_pkg_init_wf.

```

---

## Preliminary: hash function

The first thing we need to take care of is deal with the hash function. Goose doesn't support any proper hash function (yet), so we implement a fairly bad one by hand for this example. We need it to be a function from `w32 → w32` (it doesn't matter which one), and for the proof we actually need to write down that function explicitly since it's important that it be a fixed one.

```rocq
(* This was derived from seeing the expression in the proof of [wp_hash]. It is
important that there be a fixed hash function, but it's not important for
correctness what it is. *)
Definition hash_f (w: w32) : w32 :=
  (word.add
     (word.mul
        (word.add
           (word.mul
              (word.add
                 (word.mul
                    (word.add (word.mul (W32 5381) (W32 17000069))
                       (word.and w (W32 255)))
                    (W32 17000069))
                 (word.and
                    (word.sru w
                       (W32 8))
                    (W32 255)))
              (W32 17000069))
           (word.and (word.sru w (W32 16)) (W32 255)))
        (W32 17000069))
     (word.and (word.sru w (W32 24)) (W32 255))).

Lemma wp_hash (w: w32) :
  {{{ is_pkg_init sharded_hashmap }}}
    @! sharded_hashmap.hash #w
  {{{ RET #(hash_f w); True }}}.
Proof.
  wp_start as "_".
  wp_auto.
  iApply "HΦ".
  done.
Qed.

```

We will not need to use the definition of `hash_f` at all, and for performance reasons it helps to make it opaque.

```rocq
Typeclasses Opaque hash_f.
Opaque hash_f.

```

---

## Bucket theory

The next development is to develop a theory for how the keyspace is divided among hash buckets.

```rocq
Definition hash_bucket (key: w32) (max_buckets: Z) : Z :=
  uint.Z (hash_f key) `mod` max_buckets.

Hint Unfold hash_bucket : word.

Lemma hash_bucket_bound key max_buckets :
  0 < max_buckets →
  0 ≤ hash_bucket key max_buckets < max_buckets.
Proof.
  word.
Qed.

```

`bucket_map` is the key definition of this section: it groups a set of keys (the ones actually being used, rather than all possible w32 values) into a map from bucket index to the keys owned by that bucket.

The way this is defined is a bit complicated, but the theorems `bucket_map_lookup_None` and `bucket_map_lookup_Some` are fairly easy to use.

```rocq
Definition bucket_map (m: gset w32) (max_buckets: Z) : gmap Z (gset w32) :=
  list_to_map ((λ (i: Z),
               (i, filter (λ k, hash_bucket k max_buckets = i) m)
               ) <$> seqZ 0 max_buckets).

Lemma bucket_map_lookup_None m max_buckets (i: Z) :
  ~(0 ≤ i < max_buckets) →
  bucket_map m max_buckets !! i = None.
Proof.
  intros.
  apply not_elem_of_list_to_map.
  set_solver by lia.
Qed.

Lemma bucket_map_lookup_Some m max_buckets (i: Z) :
  0 ≤ i < max_buckets →
  bucket_map m max_buckets !! i = Some (filter (λ k, hash_bucket k max_buckets = i) m).
Proof.
  intros Hbound.
  rewrite /bucket_map.
  apply elem_of_list_to_map.
  { (* NoDup *)
    rewrite -list_fmap_compose.
    rewrite list_fmap_id.
    apply NoDup_seqZ.
  }
  set_solver by lia.
Qed.

```

**Exercise:** Prove this theorem using the two above. _(10 points)_

```rocq
Lemma bucket_map_lookup_Some_iff m max_buckets (i: Z) s :
  bucket_map m max_buckets !! i = Some s →
  s = filter (λ k, hash_bucket k max_buckets = i) m.
Proof.
  intros Heq.
Admitted.
```

---

## Hashmap-specific ghost theory

The hashmap proof is based on two assertions: `hashmap_auth γ max_buckets m` which holds the global (logical) state of the hashmap `m`, and `hashmap_sub γ hash_idx sub_m` which owns a part of the map `sub_m` that corresponds to the keys in bucket `hash_idx`.

Note that the only physical correspondences are that `sub_m` is held in the physical state of a bucket (stored in a Go `*shard`) protected by the bucket's lock, and `max_buckets` is the length of the buckets array in a hashmap. The other variables are logical: a bucket does not track which index it has in the code, and the full map is only the collection of all the sub-maps and is never locked by one thread.

This section develops just a ghost theory for these assertions (no code is involved). The ghost state underlying these assertions is a bit intricate so it really helps to isolate the proofs.

The hashmap predicates will use `γ: ghost_names`, which is actually a record of three names, one for each ghost variable used to define this library.

- `user_name` is used for the own_sharded_map that the caller will use.
- `map_name` is of type `auth_mapR w32 w64`. The authoritative part is the global map contents, while the fragments represent the shards for each bucket.
- `buckets_name` is of type `auth_mapR Z (gset w32)`. The fragment `{[idx := s]}` asserts that bucket index `idx` holds keys `s` from the global map; these will all have `hash(k) % max_buckets = idx`. The authoritative part tracks the full assignment of keys to buckets, which is calculated by applying `bucket_map` to the global map in `hashmap_auth`.

```rocq
Record ghost_names := mkNames {
    user_name : gname;
    map_name : gname;
    buckets_name : gname;
  }.

Definition own_sharded_map (γ: ghost_names) (m: gmap w32 w64) :=
  ghost_var γ.(user_name) (DfracOwn (1/2)) m.

Definition hashmap_auth (γ: ghost_names) (max_buckets: Z) (m: gmap w32 w64) : iProp Σ :=
    "%Hoverflow" :: ⌜0 < max_buckets < 2^32⌝ ∗
    "Hmap_auth" :: auth_map.auth_map_auth (map_name γ) m ∗
    "Hbuckets_auth" :: auth_map.auth_map_auth (buckets_name γ) (bucket_map (dom m) max_buckets).

Definition hashmap_sub (γ: ghost_names) (hash_idx: Z) (sub_m: gmap w32 w64) : iProp Σ :=
    "Hmap_frag" :: auth_map.auth_map_frag (map_name γ) sub_m ∗
    "Hbucket_frag" :: auth_map.auth_map_frag (buckets_name γ) {[hash_idx:=dom sub_m]}.

```

We initialize the hashmap state via the intermediate assertion `hashmap_pre_auth`, which is almost `hashmap_auth` but doesn't require non-zero buckets (so we can start out with an empty list of buckets).

```rocq
Definition hashmap_pre_auth (γ: ghost_names) (num_buckets: Z): iProp Σ :=
  "%Hpos" :: ⌜0 ≤ num_buckets⌝ ∗
  "Hm_var" ∷ ghost_var γ.(user_name) (DfracOwn (1/2)) (∅: gmap w32 w64) ∗
  "Hmap_auth" :: auth_map.auth_map_auth (map_name γ) (∅: gmap w32 w64) ∗
  "Hbuckets_auth" :: auth_map.auth_map_auth (buckets_name γ) (bucket_map ∅ num_buckets).

Lemma hashmap_pre_auth_init :
  ⊢ |==> ∃ γ, hashmap_pre_auth γ 0 ∗ own_sharded_map γ ∅.
Proof.
  iMod (ghost_var_alloc (∅ : gmap w32 w64)) as (user_γ) "[Hm_user Hm_var]".
  iMod (auth_map.auth_map_init (K:=w32) (A:=w64)) as (map_γ) "Hmap_auth".
  iMod (auth_map.auth_map_init (K:=Z) (A:=gset w32)) as (bucket_γ) "Hbucket_auth".
  iModIntro.
  iExists (mkNames user_γ map_γ bucket_γ).
  iFrame.
  iPureIntro. lia.
Qed.

Lemma seqZ_plus_one (m n: Z) :
  0 ≤ m →
  seqZ n (m + 1) = seqZ n m ++ [n + m].
Proof.
  intros H.
  rewrite seqZ_app //.
Qed.

(* this is what wp_createNewBuckets uses to add one more bucket to the end *)
Lemma hashmap_pre_auth_alloc_bucket (γ: ghost_names) (num_buckets:  Z) :
  hashmap_pre_auth γ num_buckets ==∗ hashmap_pre_auth γ (num_buckets + 1) ∗ hashmap_sub γ num_buckets ∅.
Proof.
  iIntros "H". iNamed "H".
  iDestruct (auth_map.auth_map_alloc_empty with "Hmap_auth") as "[Hmap_auth Hmap_frag]".
  iMod (auth_map.auth_map_alloc1 num_buckets (∅ : gset w32) with "[$Hbuckets_auth]")
          as "[Hbuckets_auth Hbucket_frag]".
  { rewrite dom_list_to_map_L.
    set_solver by lia. }
  iFrame "Hm_var Hmap_auth Hmap_frag Hbucket_frag".
  iModIntro.
  iSplit.
  { iPureIntro. lia. }
  rewrite /named. iExactEq "Hbuckets_auth".
  f_equal.
  rewrite /bucket_map.
  (* the basic idea is that the left-hand side is an insertion into a map constructed from a list, while the right-hand side appends to a list and then constructs a map; these do the same thing in a different order *)
  rewrite -> seqZ_plus_one by lia.
  (* this just makes the goal more readable *)
  change (filter _ ∅) with (∅ : gset w32).
  replace (0 + num_buckets) with num_buckets by lia.
  rewrite fmap_app /=.
  rewrite list_to_map_app /=.
  rewrite insert_empty.
  rewrite -insert_union_singleton_r //.
  apply not_elem_of_dom.
  rewrite dom_list_to_map_L.
  set_solver by lia.
Qed.

Lemma hashmap_pre_auth_finish (γ: ghost_names) (num_buckets: Z) :
  0 < num_buckets < 2^32 →
  hashmap_pre_auth γ num_buckets -∗
  hashmap_auth γ num_buckets ∅ ∗
    ghost_var γ.(user_name) (DfracOwn (1 / 2)) (∅: gmap w32 w64).
Proof.
  intros Hoverflow.
  iIntros "H". iNamed "H".
  iFrame. iPureIntro. lia.
Qed.

Lemma hashmap_auth_sub_valid γ m max_buckets sub_m hash_idx :
  hashmap_auth γ max_buckets m ∗ hashmap_sub γ hash_idx sub_m -∗
    ⌜0 < max_buckets < 2^32 ∧ sub_m ⊆ m ∧
    dom sub_m = filter (λ k, hash_bucket k max_buckets = hash_idx) (dom m)⌝.
Proof.
  iIntros "[Hauth Hfrag]". iNamed "Hauth"; iNamed "Hfrag".
  iDestruct (auth_map.auth_map_frag_subset with
              "Hmap_auth Hmap_frag") as %Hsub.
  iDestruct (auth_map.auth_map_frag_subset with
              "Hbuckets_auth Hbucket_frag") as %Hsub_buckets.
  iPureIntro.
  split; auto.
  apply map_singleton_subseteq_l in Hsub_buckets.
  apply bucket_map_lookup_Some_iff in Hsub_buckets.
  auto.
Qed.

```

**Exercise:** prove `map_get_subset` below. _(20 points)_

The pure theorem captures a tricky part of sharding: if in `Load` we return `(0, false)` (reporting that a key was not found), we need to prove that the key would also not be found in the global hashmap.

Think about why you believe this is true based on how the hashmap works before doing this proof.

I used these theorems:

- `map_get_true`, `map_get_false`
- `not_elem_of_dom` (also see `not_elem_of_dom_1` and `not_elem_of_dom_2`)
- `elem_of_filter`

I also used `contradict H` where `H: k ∉ dom m` to switch to proving `k ∈ dom m` (thus doing a proof by contradiction).

```rocq
Lemma map_get_subset (m sub_m: gmap w32 w64) (numBuckets: Z) (idx: Z) (key: w32) :
  0 < numBuckets < 2^32 →
  sub_m ⊆ m →
  idx = hash_bucket key numBuckets →
  dom sub_m =
    filter (λ k : w32, hash_bucket k numBuckets = idx)
      (dom m) →
  m !! key = sub_m !! key.
Proof.
  intros Hbound Hsub Hidx Hsub_m.
  destruct (sub_m !! key) eqn:Hget.
Admitted.

```

This theorem captures the essence of why `Load` is correct. The hard work is all in `map_get_subset`.

```rocq
Lemma hashmap_auth_sub_get γ m max_buckets sub_m hash_idx key :
  hash_idx = hash_bucket key max_buckets →
  hashmap_auth γ max_buckets m ∗ hashmap_sub γ hash_idx sub_m -∗
    ⌜m !! key = sub_m !! key⌝.
Proof.
  iIntros (Hidx) "[Hauth Hfrag]".
  iDestruct (hashmap_auth_sub_valid with "[$Hauth $Hfrag]") as %Hvalid;
    destruct_and! Hvalid.
  iPureIntro.
  eapply map_get_subset; eauto.
Qed.

```

This proof captures some details of how the bucket assignment changes when we insert into the map. Since the buckets only hold keys actually in the map (as opposed to all $2^{32}$ possible keys) this is non-trivial.

```rocq
Lemma bucket_map_insert (m : gmap w32 w64) (max_buckets : Z) (sub_m : gmap w32 w64)
    (hash_idx : Z) (key : w32) :
  0 < max_buckets →
  hash_bucket key max_buckets = hash_idx →
  dom sub_m = filter (λ k, hash_bucket k max_buckets = hash_idx) (dom m) →
  <[hash_idx:={[key]} ∪ dom sub_m]> (bucket_map (dom m) max_buckets) =
  bucket_map ({[key]} ∪ dom m) max_buckets.
Proof.
  intros Hoverflow Hidx Hsub_dom.
  apply map_eq.
  intros idx.
  destruct (decide (0 ≤ idx < max_buckets)).
  - rewrite bucket_map_lookup_Some //.
    destruct (decide (idx = hash_idx)).
    { subst.
      rewrite lookup_insert_eq.
      f_equal.
      set_solver. }
    rewrite lookup_insert_ne //.
    rewrite bucket_map_lookup_Some //.
    f_equal.
    rewrite filter_union_L.
    rewrite filter_singleton_False_L.
    { congruence. }
    set_solver.
  - rewrite lookup_insert_ne.
    { word. }
    rewrite !bucket_map_lookup_None //.
Qed.

```

**Exercise:** finish the proof of `hashmap_auth_sub_insert` below. _(25 points)_

Inserting into a sub-map is fairly sophisticated. This proof is divided into two almost completely different sub-proofs.

To complete this proof you should read the partial proof provided and understand what part is missing in order to understand what you need to do. Remember that there are lemmas proven above; these are a big hint, they must be used somewhere!

This is probably the hardest part of the assignment.

```rocq
Lemma hashmap_auth_sub_insert γ m max_buckets sub_m hash_idx key v :
  hash_bucket key max_buckets = hash_idx →
  hashmap_auth γ max_buckets m ∗ hashmap_sub γ hash_idx sub_m ==∗
  hashmap_auth γ max_buckets (<[key := v]> m) ∗ hashmap_sub γ hash_idx (<[key := v]> sub_m).
Proof.
  iIntros (Hidx) "[Hauth Hfrag]".
  iDestruct (hashmap_auth_sub_valid with "[$Hauth $Hfrag]") as %Hvalid.
  destruct Hvalid as (Hoverflow0 & Hsub & Hsub_dom).
  iNamed "Hauth". iNamed "Hfrag".

  (* the change to the bucket variable depends on whether this is an update or a
  new insertion *)
  destruct (decide (key ∈ dom m)).
  {
```

Case 1: updating a key already in the map, and hence in sub_m (due to its hash bucket). First, insert it into the map ghost variable.

```rocq
    rewrite /hashmap_auth /hashmap_sub.
    iFrame (Hoverflow).
    iMod (auth_map.auth_map_insert_map key v with "[$Hmap_auth $Hmap_frag]") as "[Hmap_auth Hmap_frag]".
    {
      rewrite Hsub_dom.
      apply elem_of_filter.
      eauto.
    }
    iFrame "Hmap_auth Hmap_frag".

    (* Now we need to deal with the bucket map. It's actually unchanged by this insertion; we just need to prove these equalities. *)
    rewrite /hashmap_auth /hashmap_sub.
    iModIntro.
    assert (dom (<[key:=v]> m) = dom m) as Hdom_m.
    { set_solver. }
    rewrite Hdom_m. iFrame "Hbuckets_auth".
    assert (dom (<[key:=v]> sub_m) = dom sub_m) as Hdom_sub_m.
    { set_solver. }
    rewrite Hdom_sub_m.
    iFrame.
  }
  {
```

Case 2: inserting a new key.

The first part of this proof (updating the map variable) mirrors the other case. In the second part you'll need to also update the bucket ghost variable.

```rocq
    rewrite /hashmap_auth /hashmap_sub.
    iFrame (Hoverflow).

    admit.
  }
Admitted.
```

---

## Abstract representation

Finally we get to the invariants for the atomic specification.

```rocq
Definition lock_inv (γ: ghost_names) (hash_idx: Z) (map_l: loc): iProp Σ :=
  ∃ (sub_m: gmap w32 w64),
    "HsubMap" :: map_l ↦$ sub_m ∗
    "Hfrag" :: hashmap_sub γ hash_idx sub_m.

Definition is_bucket (γ: ghost_names) (l: loc) (hash_idx: Z) : iProp Σ :=
  ∃ (mu_l subMap_l: loc),
  "#subMap" :: l ↦s[sharded_hashmap.bucket :: "subMap"]□ subMap_l ∗
  "#mu" :: l ↦s[sharded_hashmap.bucket :: "mu"]□ mu_l ∗
  "#Hlock" :: is_Mutex mu_l (lock_inv γ hash_idx subMap_l).

```

One of the most interesting parts of this definition is how we manage the ownership of `ghost_var γ.(user_name)`, which holds the logical state of the map as seen by the user. (Remember that `own_sharded_map γ m` is just a half of this ghost variable.)

Since the hashmap isn't protected by one lock but by several, where do we put `γ.(user_name)`? We will use an _invariant_ `inv N P`. Remember that once we create this invariant, `P` needs to hold at all intermediate points of the program. There is a dedicated tactic `iInv` for accessing an invariant in a proof, which we can do as a ghost step at any time.

```rocq
Let N := nroot .@ "sharded_hashmap".

Definition is_hashmap (γ: ghost_names) (l: loc) :=
  (∃ (b_s: slice.t) (b_ls: list loc),
  "#buckets" :: l ↦s[sharded_hashmap.HashMap :: "buckets"]□ b_s ∗
  "#Hb_ls" :: own_slice b_s (DfracDiscarded) b_ls ∗
  "%Hsz32" :: ⌜0 < uint.Z (slice.len_f b_s) < 2^32⌝ ∗
  "His_buckets" :: ([∗ list] i↦bucket_l ∈ b_ls,
    is_bucket γ bucket_l (Z.of_nat i)
  ) ∗
  "#His_inv" :: inv N (∃ (m: gmap w32 w64),
      "Hm_var" :: ghost_var γ.(user_name) (DfracOwn (1/2)) m ∗
      "Hauth" :: hashmap_auth γ (uint.Z (slice.len_f b_s)) m
  ))%I.

```

## Program proofs

With all that theory and abstraction relation setup done, we can finally start verifying some code.

### Initialization

It turns out initializing the hashmap is a huge pain, both dealing with the loops and setting up all this ghost state. You'll only verify a small part of it.

```rocq
Lemma wp_newBucket (hash_idx: Z) (γ: ghost_names) :
  {{{ is_pkg_init sharded_hashmap ∗ hashmap_sub γ hash_idx ∅ }}}
    @! sharded_hashmap.newBucket #()
  {{{ (b_l: loc), RET #b_l; is_bucket γ b_l hash_idx }}}.
Proof.
  wp_start as "Hfrag".
  wp_alloc m_l as "mu".
  wp_auto.
  wp_apply wp_map_make.
  { done. }
  iIntros (s_l) "Hshard".
  wp_auto.
  wp_alloc b_l as "H". iApply struct_fields_split in "H". iNamed "H".
  iSimpl in "Hmu HsubMap".
  iPersist "Hmu HsubMap".
  iMod (init_Mutex (lock_inv γ hash_idx s_l) with
         "mu [Hfrag Hshard]") as "Hlock".
  { iModIntro. rewrite /lock_inv.
    iExists (∅). iFrame. }
  wp_auto. wp_finish. iFrame "#∗".
Qed.

Lemma wp_createNewBuckets (γ: ghost_names) (newSize: w32) :
  {{{ is_pkg_init sharded_hashmap ∗ ⌜0 < uint.Z newSize⌝ ∗
      hashmap_pre_auth γ 0
  }}}
    @! sharded_hashmap.createNewBuckets #newSize
  {{{ (s: slice.t) (b_ls: list loc), RET #s;
      "Hauth" :: hashmap_pre_auth γ (uint.Z newSize) ∗
      "Hown_buckets" :: own_slice s (DfracOwn 1) b_ls ∗
      "His_buckets" :: ([∗ list] i↦bucket_l ∈ b_ls,
        is_bucket γ bucket_l (Z.of_nat i)
      ) ∗
      "%Hlen" :: ⌜length b_ls = uint.nat newSize⌝
  }}}.
Proof.
  wp_start as "(%Hpos & Hauth)".
  wp_auto.
  iPersist "numBuckets newSize".
  iAssert (∃ (i: w64) (s: slice.t) (b_ls: list loc),
                  "i" :: i_ptr ↦ i ∗
                  "%Hi_bound" :: ⌜0 ≤ uint.Z i ≤ uint.Z newSize⌝ ∗
                  "Hauth" :: hashmap_pre_auth γ (uint.Z i) ∗
                  "newBuckets" :: newBuckets_ptr ↦ s ∗
                  "Hown_buckets" :: s ↦* b_ls ∗
                  "Hbucket_cap" :: own_slice_cap loc s (DfracOwn 1) ∗
                  "%Hi" :: ⌜length b_ls = uint.nat i⌝ ∗
                  "His_buckets" :: ([∗ list] i'↦bucket_l ∈ b_ls,
                    is_bucket γ bucket_l (Z.of_nat i'))
              )%I with "[$i $newBuckets $Hauth]" as "HI".
  { iExists [].
    iDestruct (own_slice_nil) as "$".
    iDestruct (own_slice_cap_nil) as "$".
    simpl.
    iPureIntro. word.
  }
  wp_for "HI".
  wp_if_destruct.
  { iMod (hashmap_pre_auth_alloc_bucket with "[$Hauth]") as "[Hauth Hsub]".
    wp_apply (wp_newBucket (uint.Z i) with "[$Hsub]").
    iIntros (b_l) "Hbucket".
    wp_auto.
    wp_apply wp_slice_literal. iIntros (s') "Hnew_bucket".
    wp_auto.
    wp_apply (wp_slice_append with "[Hown_buckets $Hbucket_cap Hnew_bucket]").
    { iFrame. }
    iIntros (s'') "(Hown_buckets & Hbucket_cap & Hnew_bucket)".
    wp_auto.
    wp_for_post.
    iFrame "HΦ".
    iFrame "i".
    replace (uint.Z (word.add i (W64 1))) with (uint.Z i + 1) by word.
    replace (uint.Z (W64 (uint.Z newSize))) with (uint.Z newSize) in * by word.
    iFrame "Hauth".
    iFrame "newBuckets Hown_buckets Hbucket_cap".
    simpl.
    iSplit.
    { word. }
    iSplit.
    { len. }
    rewrite big_sepL_app /=.
    replace (Z.of_nat (length b_ls + 0)) with (uint.Z i) by word.
    iFrame "His_buckets Hbucket".
  }
  wp_finish.
  iFrame.
  replace (uint.Z i) with (uint.Z newSize) by word.
  iFrame "Hauth".
  iPureIntro. word.
Qed.

```

This theorem ties everything together to initialize the hashmap.

**Exercise:** finish the proof of `wp_NewHashMap`. _(10 points)_

You'll need to create the invariant above. Use the theorem `inv_alloc` with the `iMod` tactic:

```
  iMod (inv_alloc N _ (∃ (m: gmap w32 w64),
      "Hm_var" :: ghost_var γ.(user_name) (DfracOwn (1/2)) m ∗
      "Hauth" :: hashmap_auth γ (uint.Z (Slice.sz b_s)) m
  )%I with "[H1 H2 H3]") as "Hinv".
```

You'll need to replace `H1 H2 H3` with whatever hypotheses are needed to prove the invariant initially. The invariant needs to match what's in `is_hashmap` so I've given it to you above, it's only a small hint.

```rocq
Lemma wp_NewHashmap (hm_l: loc) (size: w32) :
  {{{ is_pkg_init sharded_hashmap ∗ ⌜0 < uint.Z size⌝ }}}
    @! sharded_hashmap.NewHashMap #size
  {{{ (hm_l: loc) (γ: ghost_names), RET #hm_l;
      is_hashmap γ hm_l ∗ own_sharded_map γ ∅
  }}}.
Proof.
  wp_start as "%Hpos".
  wp_auto.
  iMod (hashmap_pre_auth_init) as (γ) "[Hpre Huser]".
Admitted.

Lemma wp_bucketIdx (key: w32) (numBuckets: w64) :
  {{{ is_pkg_init sharded_hashmap ∗ ⌜0 < uint.Z numBuckets < 2^32⌝ }}}
    @! sharded_hashmap.bucketIdx #key #numBuckets
  {{{ (idx: w64), RET #idx; ⌜uint.Z idx = hash_bucket key (uint.Z numBuckets)⌝ }}}.
Proof.
  wp_start as "%Hnonzero".
  wp_auto.
  wp_apply wp_hash.
  iApply "HΦ".
  iPureIntro.
  rewrite /hash_bucket.
  rewrite -> word.unsigned_modu_nowrap by word.
  replace (uint.Z (W32 (uint.Z numBuckets))) with (uint.Z numBuckets) by word.
  word.
Qed.

```

### Load and Store

Once initialized, our hashmap has just two key operations: `Load` and `Store`.

:::

```rocq
Lemma wp_HashMap__Load (hm_l: loc) γ (key: w32) :
  ∀ (Φ: val → iProp Σ),
  (is_pkg_init sharded_hashmap ∗ is_hashmap γ hm_l ∗
      |={⊤ ∖ ↑N,∅}=> ∃ (m: gmap w32 w64), own_sharded_map γ m ∗
          (own_sharded_map γ m ={∅,⊤ ∖ ↑N}=∗
            Φ (#(default (W64 0) (m !! key)), #(bool_decide (is_Some (m !! key))))%V
  )) -∗
    WP hm_l @ (ptrT.id sharded_hashmap.HashMap.id) @ "Load" #key {{ Φ }}.
Proof.
  iIntros (Φ) "(#? & #Hm & Hau)".
  wp_method_call. wp_call.
  iNamed "Hm".
  wp_auto.
  wp_alloc buckets_ptr as "Hbuckets".
  wp_auto.
  iDestruct (own_slice_len with "Hb_ls") as %Hlen.
  wp_apply wp_bucketIdx.
  { iPureIntro. word. }
  iIntros (idx Hidx).
  list_elem b_ls (sint.nat idx) as bi_l.
  wp_auto.
  wp_pure.
  { word. }
  wp_apply (wp_load_slice_elem with "[$Hb_ls]").
  { word. }
  { eauto. }
  iIntros "_".
  wp_auto.
  iDestruct (big_sepL_lookup _ _ (sint.nat idx) with "His_buckets") as "Hidx".
  { eauto. }
  replace (Z.of_nat (sint.nat idx)) with (sint.Z idx) by word.
  replace (uint.Z idx) with (sint.Z idx) in Hidx by word.
  iNamed "Hidx".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hlock]").
  iIntros "[locked Hlock_inv]". iNamed "Hlock_inv".

  (* start of critical section *)
  wp_auto.
  wp_apply (wp_map_get with "[$HsubMap]").
  iIntros "HsubMap".
  wp_auto.

  (* use user's atomic update on abstract state *)
  (* Some boilerplate is needed to make this work, but notice that at the end, we get several hypotheses with the suffix "_inv", which come from "opening" the invariant. The goal has `|={⊤ ∖ ↑N, ⊤}=>`, which represents that the invariant N is unavailable and must be restored to proceed. We'll do that with "Hclose_inv", which requires re-proving the invariant. *)
  iApply fupd_wp.
  iInv "His_inv" as ">HI" "Hclose_inv".
  iNamedSuffix "HI" "_inv".

  (* The purpose of opening the invariant is to use the atomic update from the caller, so we do that before closing. *)
  iMod "Hau" as (m0) "[Hown Hclose_au]".

  iDestruct (hashmap_auth_sub_get with "[$Hauth_inv $Hfrag]") as %Hget'.
  { eauto. }
  iDestruct (ghost_var_agree with "Hm_var_inv Hown") as %<-.
  rewrite Hget'.
  (* finish firing the AU *)
  iMod ("Hclose_au" with "Hown") as "HΦ".

  (* Now we are done with the invariant and need several more tactics to close it back up. Since this operation is read-only, the proof of the invariant afterward is just iFrame. *)
  iMod ("Hclose_inv" with "[Hm_var_inv Hauth_inv]").
  { iModIntro. iFrame. }
  iModIntro.

  wp_apply (wp_Mutex__Unlock with "[$locked $Hlock $Hfrag $HsubMap]").
  iApply "HΦ".
Qed.

```

**Exercise:** prove `wp_HashMap__Store`. _(10 points)_

The code and proof for `Store` are very similar to that of `Load` so you should be able to figure this out from reading the proof above.

```rocq
Lemma wp_HashMap__Store (hm_l: loc) γ (key: w32) (v: w64) :
  ∀ Φ,
  (is_pkg_init sharded_hashmap ∗ is_hashmap γ hm_l ∗
      (|={⊤ ∖ ↑N,∅}=> ∃ m, own_sharded_map γ m ∗
          (own_sharded_map γ (<[key := v]> m) ={∅,⊤ ∖ ↑N}=∗ Φ #()))) -∗
    WP hm_l @ (ptrT.id sharded_hashmap.HashMap.id) @ "Store" #key #v {{ Φ }}.
Proof.
Admitted.
```

After understanding the proof, how would you use it to explain to someone how per-bucket locking works? What changed from your previous explanation? **Exercise:** Write this down in a Rocq comment in your solution. _(15 points)_

```rocq
End proof.
```
