---
# Auto-generated from literate source. DO NOT EDIT.
category: assignment
tags: literate
order: 5
icon: file-lines
shortTitle: "Assignment 4"
---

# Assignment 4: concurrent sharded hash map

In this assignment, you'll finish the proof of a concurrent, sharded hash map. You'll only be doing proofs: all theorem statements and invariants are provided. Substantial proof is already provided, which means you'll spend more time reading code than writing it.

You should start by reading and understanding the [code](https://github.com/tchajed/sys-verif-fa24-proofs/blob/main/go/sharded_hashmap/sharded_hashmap.go). Really! Go read it! And spend some time figure out why you think it works and how you would explain its correctness without any of the tools in this proof. **Exercise:** Write this down in a Coq comment in your solution. _(10 points)_

I suggest you do a quick skim over everything to understand the ideas and intuition, especially compared to just blindly trying to fill in proofs. The sub-sections should also be fairly independent so feel free to skip around to avoid getting stuck for too long on one part; it's better you attempt every part than finish some proofs and never start the others.

A secondary goal is for you to _understand_ this proof, so keep that in the back of your mind. After understanding the proof, how would you use it to explain to someone how per-bucket locking works? What changed from your previous explanation? **Exercise:** Write this down in a Coq comment in your solution. _(10 points)_

```coq
From sys_verif.program_proof Require Import prelude empty_ffi.
From iris.algebra Require Import ofe auth excl gmap.
From Goose.sys_verif_code Require Import sharded_hashmap.

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

```coq
Module auth_map.


```

A good deal of boilerplate is needed to create a resource algebra. The interesting parts are just `auth_mapR` (this is the algebraic structure, defined using existing structures), `auth_map_auth_def`, and `auth_map_frag_def`.

```coq
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

```coq
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
    { rewrite map_fmap_union //. }
    apply map_disjoint_fmap; auto.
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
    { rewrite map_fmap_union. iIntros "$". }
    apply map_disjoint_fmap; auto.
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
    { rewrite Hgetm /= in Hin.
      apply Excl_included in Hin.
      congruence. }
    apply Some_included_is_Some in Hin.
    rewrite Hgetm /= in Hin. destruct Hin; congruence.
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
    apply gmap.alloc_local_update; [ | done ].
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
    apply gmap.singleton_local_update_any.
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
      rewrite insert_delete_insert.
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
    rewrite insert_insert.
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
Context `{hG: !heapGS Σ}.
Context `{hG1: !auth_map.auth_mapG Σ w32 w64}.
Context `{hG2: !auth_map.auth_mapG Σ Z (gset w32)}.

```

---

## Preliminary: hash function

The first thing we need to take care of is deal with the hash function. Goose doesn't support any proper hash function (yet), so we implement a fairly bad one by hand for this example. We need it to be a function from `w32 → w32` (it doesn't matter which one), and for the proof we actually need to write down that function explicitly since it's important that it be a fixed one.

```coq
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
  {{{ True }}}
    hash #w
  {{{ RET #(hash_f w); True }}}.
Proof.
  wp_start as "_".
  wp_alloc h_l as "h".
  wp_pures.
  repeat (wp_load || wp_store).
  iModIntro.
  iApply "HΦ".
  done.
Qed.

```

We will not need to use the definition of `hash_f` at all, and for performance reasons it helps to make it opaque.

```coq
Typeclasses Opaque hash_f.
Opaque hash_f.

```

---

## shard library

This hashmap has a fixed number of buckets, each of which is a _shard_ of the overall map. A shard can have several entries. We use a regular, non-concurrent Go map to store these for convenience, but we still wrap the use of that map in a small "shard" library. Here we prove specs for that library, mostly delegating to the Goose map specs.

We also deal with the fact that Goose only supports maps from `uint64` but we want one from `uint32` here.

```coq
Definition own_shard (s_l: loc) (m: gmap w32 w64) : iProp Σ :=
  ∃ (m_l: loc) (m64: gmap w64 w64),
    "%Hvals" :: ⌜(∀ (k: w32) (v: w64),
                    m !! k = Some v ↔ m64 !! (W64 (uint.Z k)) = Some v)⌝ ∗
    "m" :: s_l ↦[shard :: "m"] #m_l ∗
    "Hm" :: own_map m_l (DfracOwn 1) m64.

Lemma wp_newShard :
  {{{ True }}}
    newShard #()
  {{{ (s_l: loc), RET #s_l; own_shard s_l ∅ }}}.
Proof.
  wp_start as "_".
  wp_apply (wp_NewMap).
  iIntros (m_l) "Hm".
  wp_alloc s_l as "s".
  iApply struct_fields_split in "s". iNamed "s".
  iApply "HΦ".
  iFrame.
  iPureIntro.
  intros.
  rewrite !lookup_empty. auto.
Qed.

```

**Exercise:** finish up the proofs of `wp_shard__Load` and `wp_shard__Store` _(10 points)_

```coq
Lemma wp_shard__Load (s_l: loc) (key: w32) (m: gmap w32 w64) :
  {{{ own_shard s_l m }}}
    shard__Load #s_l #key
  {{{ (v: w64) (ok: bool), RET (#v, #ok);
      own_shard s_l m ∗
      ⌜(v, ok) = map_get m key⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_loadField.
  wp_apply (wp_MapGet with "[$Hm]").
  iIntros (v ok) "(%Hget & Hm)".
  wp_pures.
  iModIntro. iApply "HΦ". iFrame.
  iPureIntro.
  split.
  - auto.
  - rewrite /map_get. simpl.
    rewrite /map_get in Hget. simpl in Hget.
    destruct (m !! key) eqn:Hm.
(* FILL IN HERE *)
    + admit.
    + admit.
Admitted.

Lemma wp_shard__Store (s_l: loc) (key: w32) (val: w64) (m: gmap w32 w64) :
  {{{ own_shard s_l m }}}
    shard__Store #s_l #key #val
  {{{ RET #();
      own_shard s_l (<[ key := val ]> m)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapInsert with "[$Hm]").
  { eauto. }
  iIntros "Hm".
  rewrite /typed_map.map_insert.
  wp_pures. iModIntro. iApply "HΦ".
  rewrite /own_shard.
  iFrame.
  iPureIntro.
  intros.
  destruct (decide (k = key)); subst.
  - admit.
  - rewrite !lookup_insert_ne //.
    (* this requires some extra work due to limitations in [word] (probably
    related to 32-bit integers) *)
    intros H.
    contradict n.
    apply (f_equal uint.Z) in H.
    word.
Admitted.
```

---

## Bucket theory

The next development is to develop a theory for how the keyspace is divided among hash buckets.

```coq
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

```coq
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

**Exercise:** Prove this theorem using the two above. _(5 points)_

```coq
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

The hashmap predicates will use `γ: ghost_names`, which is actually a record of two names, one for each ghost variable used to define this library.

- `map_name` is of type `auth_mapR w32 w64`. The authoritative part is the global map contents, while the fragments represent the shards for each bucket.
- `buckets_name` is of type `auth_mapR Z (gset w32)`. The fragment `{[idx := s]}` asserts that bucket index `idx` holds keys `s` from the global map; these will all have `hash(k) % max_buckets = idx`. The authoritative part tracks the full assignment of keys to buckets, which is calculated by applying `bucket_map` to the global map in `hashmap_auth`.

```coq
Record ghost_names := mkNames {
    map_name : gname;
    buckets_name : gname;
  }.

Definition hashmap_auth (γ: ghost_names) (max_buckets: Z) (m: gmap w32 w64) : iProp Σ :=
    "%Hoverflow" :: ⌜0 < max_buckets < 2^32⌝ ∗
    "Hmap_auth" :: auth_map.auth_map_auth (map_name γ) m ∗
    "Hbuckets_auth" :: auth_map.auth_map_auth (buckets_name γ) (bucket_map (dom m) max_buckets).

Definition hashmap_sub (γ: ghost_names) (hash_idx: Z) (sub_m: gmap w32 w64) : iProp Σ :=
    "Hmap_frag" :: auth_map.auth_map_frag (map_name γ) sub_m ∗
    "Hbucket_frag" :: auth_map.auth_map_frag (buckets_name γ) {[hash_idx:=dom sub_m]}.

```

We initialize the hashmap state via the intermediate assertion `hashmap_pre_auth`, which is almost `hashmap_auth` but doesn't require non-zero buckets (so we can start out with an empty list of buckets).

```coq
Definition hashmap_pre_auth (γ: ghost_names) (num_buckets: Z): iProp Σ :=
  "%Hpos" :: ⌜0 ≤ num_buckets⌝ ∗
  "Hmap_auth" :: auth_map.auth_map_auth (map_name γ) (∅: gmap w32 w64) ∗
  "Hbuckets_auth" :: auth_map.auth_map_auth (buckets_name γ) (bucket_map ∅ num_buckets).

Lemma hashmap_pre_auth_init :
  ⊢ |==> ∃ γ, hashmap_pre_auth γ 0.
Proof.
  iMod (auth_map.auth_map_init (K:=w32) (A:=w64)) as (map_γ) "Hmap_auth".
  iMod (auth_map.auth_map_init (K:=Z) (A:=gset w32)) as (bucket_γ) "Hbucket_auth".
  iModIntro.
  iExists (mkNames map_γ bucket_γ).
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
  iFrame "Hmap_auth Hmap_frag Hbucket_frag".
  iModIntro.
  iSplit.
  { iPureIntro. lia. }
  rewrite /named. iExactEq "Hbuckets_auth".
  f_equal.
  rewrite /bucket_map.
  (* the basic idea is that the left-hand side is an insertion into a map constructed from a list, while the right-hand side appends to a list and then constructs a map; these do the same thing in a different order *)
  rewrite seqZ_plus_one; [ | lia ].
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
  hashmap_pre_auth γ num_buckets -∗ hashmap_auth γ num_buckets ∅.
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

```coq
Lemma map_get_subset (m sub_m: gmap w32 w64) (numBuckets: Z) (idx: Z) (key: w32) :
  0 < numBuckets < 2^32 →
  sub_m ⊆ m →
  idx = hash_bucket key numBuckets →
  dom sub_m =
    filter (λ k : w32, hash_bucket k numBuckets = idx)
      (dom m) →
  map_get m key = map_get sub_m key.
Proof.
  intros Hbound Hsub Hidx Hsub_m.
  destruct (map_get sub_m key) eqn:Hget.
  destruct b.
Admitted.

```

This theorem captures the essence of why `Load` is correct. The hard work is all in `map_get_subset`.

```coq
Lemma hashmap_auth_sub_get γ m max_buckets sub_m hash_idx key :
  hash_idx = hash_bucket key max_buckets →
  hashmap_auth γ max_buckets m ∗ hashmap_sub γ hash_idx sub_m -∗
    ⌜map_get m key = map_get sub_m key⌝.
Proof.
  iIntros (Hidx) "[Hauth Hfrag]".
  iDestruct (hashmap_auth_sub_valid with "[$Hauth $Hfrag]") as %Hvalid;
    destruct_and! Hvalid.
  iPureIntro.
  eapply map_get_subset; eauto.
Qed.

```

This proof captures some details of how the bucket assignment changes when we insert into the map. Since the buckets only hold keys actually in the map (as opposed to all $2^{32}$ possible keys) this is non-trivial.

```coq
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
      rewrite lookup_insert.
      f_equal.
      set_solver. }
    rewrite lookup_insert_ne //.
    rewrite bucket_map_lookup_Some //.
    f_equal.
    rewrite filter_union_L.
    rewrite filter_singleton_not_L.
    + set_solver.
    + congruence.
  - rewrite lookup_insert_ne.
    + rewrite !bucket_map_lookup_None //.
    + word.
Qed.

```

**Exercise:** finish the proof of `hashmap_auth_sub_insert` below. _(25 points)_

Inserting into a sub-map is fairly sophisticated. This proof is divided into two almost completely different sub-proofs.

To complete this proof you should read the partial proof provided and understand what part is missing in order to understand what you need to do. Remember that there are lemmas proven above; these are a big hint, they must be used somewhere!

This is probably the hardest part of the assignment.

```coq
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

```coq
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

```coq
    rewrite /hashmap_auth /hashmap_sub.
    iFrame (Hoverflow).

    admit.
  }
Admitted.
```

---

## Abstract representation

Finally we get to the abstract representation relation, the predicate `is_hashmap` that connects the state of the code to the logical state of the hashmap. We will use the HOCAP style of specification developed in class, so `is_hashmap` takes a `P: gmap w32 w64 → iProp Σ`.

```coq
Definition lock_inv (γ: ghost_names) (hash_idx: Z) (map_l: loc): iProp Σ :=
  ∃ (sub_m: gmap w32 w64),
    "HsubMap" :: own_shard map_l sub_m ∗
    "Hfrag" :: hashmap_sub γ hash_idx sub_m.

Definition is_bucket (γ: ghost_names) (l: loc) (hash_idx: Z) : iProp Σ :=
  ∃ (mu_l subMap_l: loc),
  "#subMap" :: l ↦[bucket :: "subMap"]□ #subMap_l ∗
  "#mu" :: l ↦[bucket :: "mu"]□ #mu_l ∗
  "#Hlock" :: is_lock nroot (#mu_l) (lock_inv γ hash_idx subMap_l).

```

One of the most interesting parts of this definition is how we use `P`. That's how the proof asserts how the code stores the abstract state of the data structure.

Since the hashmap isn't protected by one lock but by several, where do we put `P`? It turns out we need a new idea. Instead of a _lock invariant_, we'll use an _invariant_. `inv N P` is an assertion that `P` is an invariant (ignore the namespace `N` for now). An invariant isn't related to a lock; instead, `P` simply needs to hold at all intermediate points of the program, full stop (remember that a lock invariant only holds when the lock is free). Invariants are a key feature of Iris.

```coq
Definition is_hashmap (γ: ghost_names) (l: loc) (P: gmap w32 w64 → iProp Σ) :=
  (∃ (b_s: Slice.t) (b_ls: list loc),
  "#buckets" :: l ↦[HashMap :: "buckets"]□ b_s ∗
  "#Hb_ls" :: own_slice_small b_s ptrT (DfracDiscarded) b_ls ∗
  "%Hsz32" :: ⌜0 < uint.Z (Slice.sz b_s) < 2^32⌝ ∗
  "His_buckets" :: ([∗ list] i↦bucket_l ∈ b_ls,
    is_bucket γ bucket_l (Z.of_nat i)
  ) ∗
  "#His_inv" :: inv nroot (∃ (m: gmap w32 w64),
      "HP" :: P m ∗
      "Hauth" :: hashmap_auth γ (uint.Z (Slice.sz b_s)) m
  ))%I.

```

## Program proofs

With all that theory and abstraction relation setup done, we can finally start verifying some code.

### Initialization

It turns out initializing the hashmap is a huge pain, both dealing with the loops and setting up all this ghost state. You'll only verify a small part of it.

```coq
Lemma wp_newBucket (hash_idx: Z) (γ: ghost_names) :
  {{{ hashmap_sub γ hash_idx ∅ }}}
    newBucket #()
  {{{ (b_l: loc), RET #b_l; is_bucket γ b_l hash_idx }}}.
Proof.
  wp_start as "Hfrag".
  rewrite -wp_fupd.
  wp_apply (wp_new_free_lock). iIntros (m_l) "Hlock".
  wp_apply wp_newShard. iIntros (s_l) "Hshard".
  wp_alloc b_l as "H". iApply struct_fields_split in "H". iNamed "H".
  iMod (struct_field_pointsto_persist with "subMap") as "subMap".
  iMod (struct_field_pointsto_persist with "mu") as "mu".
  iMod (alloc_lock nroot _ _ (lock_inv γ hash_idx s_l) with
         "[$Hlock] [Hfrag Hshard]") as "Hlock".
  { iModIntro. rewrite /lock_inv.
    iExists (∅). iFrame. }
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma wp_createNewBuckets (γ: ghost_names) (newSize: w32) :
  {{{ ⌜0 < uint.Z newSize⌝ ∗
      hashmap_pre_auth γ 0
  }}}
    createNewBuckets #newSize
  {{{ (s: Slice.t) (b_ls: list loc), RET (slice_val s);
      "Hauth" :: hashmap_pre_auth γ (uint.Z newSize) ∗
      "Hbuckets" :: own_slice_small s ptrT (DfracOwn 1) b_ls ∗
      "His_buckets" :: ([∗ list] i↦bucket_l ∈ b_ls,
        is_bucket γ bucket_l (Z.of_nat i)
      ) ∗
      "%Hlen" :: ⌜length b_ls = uint.nat newSize⌝
  }}}.
Proof.
  wp_start as "(%Hpos & Hauth)".
  wp_apply wp_NewSlice_0. iIntros (s) "Hbuckets".
  wp_alloc newBuckets_l as "newBuckets".
  wp_alloc i_l as "i".
  wp_pures.
  wp_apply (wp_forUpto (λ i, ∃ (s: Slice.t) (b_ls: list loc),
                  "Hauth" :: hashmap_pre_auth γ (uint.Z i) ∗
                  "newBuckets" :: newBuckets_l ↦[slice.T ptrT] s ∗
                  "Hbuckets" :: own_slice s ptrT (DfracOwn 1) b_ls ∗
                  "%Hi" :: ⌜length b_ls = uint.nat i⌝ ∗
                  "His_buckets" :: ([∗ list] i'↦bucket_l ∈ b_ls,
                    is_bucket γ bucket_l (Z.of_nat i')
                  )
              )%I
             with "[] [$i $newBuckets $Hbuckets $Hauth]").
  { word. }
  {
    iIntros (i). wp_start as "(I & i & %Hi)". iNamed "I".
    iMod (hashmap_pre_auth_alloc_bucket with "[$Hauth]") as "[Hauth Hsub]".
    wp_apply (wp_newBucket (uint.Z i) with "[$Hsub]").
    iIntros (b_l) "Hbucket".
    wp_load.
    wp_apply (wp_SliceAppend with "[$Hbuckets]").
    iIntros (s') "Hbuckets".
    wp_store.
    iModIntro. iApply "HΦ". iFrame.
    replace (uint.Z (word.add i (W64 1))) with (uint.Z i + 1) by word.
    iFrame "Hauth".
    simpl.
    replace (Z.of_nat (length b_ls + 0)) with (uint.Z i) by word.
    iFrame "Hbucket".
    iPureIntro. rewrite length_app /=. word.
  }
  {
    (* prove loop invariant holds initially *)
    simpl.
    iFrame.
    iPureIntro. done.
  }
  iIntros "(IH & i)". iNamed "IH".
  assert (length b_ls = uint.nat newSize) by word.
  wp_load.
  iModIntro.
  iApply "HΦ".
  iFrame.
  iDestruct (own_slice_split with "Hbuckets") as "[$ _Hcap]".
  replace (uint.Z (W64 (uint.Z newSize))) with (uint.Z newSize) by word.
  iFrame "Hauth".
  iPureIntro. word.
Qed.

```

This theorem ties everything together to initialize the hashmap.

**Exercise:** finish the proof of `wp_NewHashMap`. _(10 points)_

You'll need to create the invariant above. Use the theorem `inv_alloc` with the `iMod` tactic:

```
  iMod (inv_alloc nroot _ (∃ (m: gmap w32 w64),
      "HP" :: P m ∗
      "Hauth" :: hashmap_auth γ (uint.Z (Slice.sz b_s)) m
  )%I with "[H1 H2 H3]") as "Hinv".
```

You'll need to replace `H1 H2 H3` with whatever hypotheses are needed to prove the invariant initially. The invariant needs to match what's in `is_hashmap` so I've given it to you above, it's only a small hint.

```coq
Lemma wp_NewHashmap (hm_l: loc) (size: w32) P :
  {{{ ⌜0 < uint.Z size⌝ ∗ P ∅ }}}
    NewHashMap #size
  {{{ (hm_l: loc) (γ: ghost_names), RET #hm_l;
      is_hashmap γ hm_l P
  }}}.
Proof.
  wp_start as "[%Hpos HP]".
  rewrite -wp_fupd.
  iMod (auth_map.auth_map_init (K:=w32) (A:=w64)) as (map_γ) "Hmap_auth".
  iMod (auth_map.auth_map_init (K:=Z) (A:=gset w32)) as (bucket_γ) "Hbucket_auth".
  (* `set` creates a variable just for the rest of the proof (notice it's in the context including its definition) *)
  set (γ := mkNames map_γ bucket_γ).
Admitted.

Lemma wp_bucketIdx (key: w32) (numBuckets: w64) :
  {{{ ⌜0 < uint.Z numBuckets < 2^32⌝ }}}
    bucketIdx #key #numBuckets
  {{{ (idx: w64), RET #idx; ⌜uint.Z idx = hash_bucket key (uint.Z numBuckets)⌝ }}}.
Proof.
  wp_start as "%Hnonzero".
  wp_apply wp_hash. wp_pures.
  iModIntro.
  iApply "HΦ".
  iPureIntro.
  rewrite /hash_bucket.
  word.
Qed.

```

### Load and Store

Once initialized, our hashmap has just two key operations: `Load` and `Store`.

::: info Timeless assumption

You can ignore `Htimeless`, but if you're curious here's why it's there.

We run into some issues with the later modality due to our setup for the HOCAP specifications and the use of an invariant. These aren't important to the presentation, so we solve them by assuming that the abstract predicate `P` is "timeless". The practical consequence is that after we open the invariant, we would ordinarily get `>I` (where `I` is the proposition for the invariant), but because `P` is timeless we can get `I` instead.

Another solution is to have the update look like `∀ m, ▷ P m -∗ |==> ▷ P m ∗ Q ...` but this is less convenient for the proof.

:::

```coq
Lemma wp_HashMap__Load (hm_l: loc) γ (key: w32) P Q {Htimeless: ∀ m, Timeless (P m)} :
  {{{ is_hashmap γ hm_l P ∗
      (∀ m, P m -∗ |==> P m ∗ Q (map_get m key))
  }}}
    HashMap__Load #hm_l #key
  {{{ (v: w64) (ok: bool), RET (#v, #ok); Q (v, ok) }}}.
Proof.
  wp_start as "[#Hm Hupd]". iNamed "Hm".
  wp_loadField.
  iDestruct (own_slice_small_sz with "Hb_ls") as %Hsz.
  wp_pures.
  wp_apply wp_slice_len.
  wp_apply wp_bucketIdx.
  { iPureIntro. word. }
  iIntros (idx Hidx).
  list_elem b_ls (uint.nat idx) as bi_l.
  wp_apply (wp_SliceGet with "[$Hb_ls]").
  { iPureIntro. eauto. }
  iIntros "_".
  wp_pures.
  iDestruct (big_sepL_lookup _ _ (uint.nat idx) with "His_buckets") as "Hidx".
  { eauto. }
  replace (Z.of_nat (uint.nat idx)) with (uint.Z idx) by word.
  iNamed "Hidx".
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "[$Hlock]").
  iIntros "[locked Hlinv]". iNamed "Hlinv".

  (* start of critical section *)
  wp_loadField.
  wp_apply (wp_shard__Load with "[$HsubMap]").
  iIntros (v ok) "[HsubMap %Hget]".
  wp_pures.
  wp_loadField.

  (* use user's ghost update on abstract state *)

```

Next comes the most interesting step: we will update the `P m` inside the invariant. To do so, we need to "open" the invariant, similar to acquiring a mutex and getting the associated lock invariant. However, since it's an invariant, we only get to open it, do ghost updates, and then have to immediately close it.

There is one other possibility, which we don't need here: it's allowed to open an invariant, then take _one step_ in the program, and then close it. This is only legal for atomic instructions (which finish in one step); since the invariant needs to hold at every intermediate step, we can't do this for more than one step, unlike locks which can be held as long as the program wants to.

We need to use `iApply fupd_wp` to make `iInv` open at a single point rather than across the next program step.

```coq
  iApply fupd_wp.
  (* the use of `>Hinv` rather than `Hinv` is a technicality related to the ▷
  modality *)
  iInv "His_inv" as ">Hinv".
```

:::: info Goal diff

```txt title="goal diff"
  Σ : gFunctors
  hG : heapGS Σ
  hG1 : auth_map.auth_mapG Σ w32 w64
  hG2 : auth_map.auth_mapG Σ Z (gset w32)
  hm_l : loc
  γ : ghost_names
  key : w32
  P : gmap w32 w64 → iPropI Σ
  Q : w64 * bool → iPropI Σ
  Htimeless : ∀ m : gmap w32 w64, Timeless (P m)
  Φ : val → iPropI Σ
  b_s : Slice.t
  b_ls : list loc
  Hsz32 : 0 < uint.Z (Slice.sz b_s) < 2 ^ 32
  Hsz : length b_ls = uint.nat (Slice.sz b_s)
  idx : w64
  Hidx : uint.Z idx = hash_bucket key (uint.Z (Slice.sz b_s))
  bi_l : loc
  Hbi_l_lookup : b_ls !! uint.nat idx = Some bi_l
  mu_l, subMap_l : loc
  sub_m : gmap w32 w64
  v : w64
  ok : bool
  Hget : (v, ok) = map_get sub_m key
  ============================
  "buckets" : hm_l ↦[HashMap::"buckets"]□ b_s
  "Hb_ls" : own_slice_small b_s ptrT DfracDiscarded b_ls
  "His_buckets" : [∗ list] i↦bucket_l ∈ b_ls, is_bucket γ bucket_l
                                                (Z.of_nat i)
  "His_inv" : inv nroot
                (∃ m : gmap w32 w64, "HP" ∷ P m ∗
                   "Hauth" ∷ hashmap_auth γ (uint.Z (Slice.sz b_s)) m)
  "subMap" : bi_l ↦[bucket::"subMap"]□ #subMap_l
  "mu" : bi_l ↦[bucket::"mu"]□ #mu_l
  "Hlock" : is_lock nroot #mu_l (lock_inv γ (uint.Z idx) subMap_l)
  --------------------------------------□
  "Hupd" : ∀ m : gmap w32 w64, P m ==∗ P m ∗ Q (map_get m key)
  "HΦ" : ∀ (v0 : w64) (ok0 : bool), Q (v0, ok0) -∗ Φ (#v0, #ok0)%V
  "locked" : lock.locked #mu_l
  "Hfrag" : hashmap_sub γ (uint.Z idx) sub_m
  "HsubMap" : own_shard subMap_l sub_m
  "Hinv" : ∃ m : gmap w32 w64, "HP" ∷ P m ∗ // [!code ++]
             "Hauth" ∷ hashmap_auth γ (uint.Z (Slice.sz b_s)) m // [!code ++]
  --------------------------------------∗
  |={⊤}=> WP Mutex__Unlock #mu_l;; (#v, #ok) {{ v, Φ v }} // [!code --]
  |={⊤ ∖ ↑nroot}=> // [!code ++]
    ▷ (∃ m : gmap w32 w64, "HP" ∷ P m ∗ // [!code ++]
         "Hauth" ∷ hashmap_auth γ (uint.Z (Slice.sz b_s)) m) ∗ // [!code ++]
    (|={⊤}=> WP Mutex__Unlock #mu_l;; (#v, #ok) {{ v, Φ v }}) // [!code ++]
```

::::

Observe the effect of opening the invariant: we obtain "Hinv" in the context, and the goal now has the form `|={E}=> (▷ I) ∗ (|={⊤}=> WP MutexUnlock ...)`.

Let's break that goal down. First, we can continue doing ghost updates, but `E = ⊤ ∖ ↑nroot` says we can't open any invariants with a name starting with `nroot` (names are hierarchical so this is all of them); this avoids us trying to open the invariant twice in the same step. We choose to give our invariant the root name since this proof doesn't require more than one invariant at any given time.

Next, `I` is now in the goal since to proceed we need to close the invariant by re-proving it.

Finally, we can proceed with the rest of the program proof after doing our work with the invariant, and possibly do more ghost updates.

```coq
  iNamed "Hinv".
  iMod ("Hupd" with "HP") as "[HP HQ]".
  iDestruct (hashmap_auth_sub_get with "[$Hauth $Hfrag]") as %Hget'.
  { eauto. }
  rewrite Hget'.
  iFrame "HP Hauth".
  iModIntro.
  iModIntro.

  wp_apply (wp_Mutex__Unlock with "[$locked $Hlock $Hfrag $HsubMap]").
  wp_pures.
  iModIntro.
  iApply "HΦ".
  rewrite -Hget. iFrame.
Qed.

```

**Exercise:** prove `wp_HashMap__Store`. _(10 points)_

The code and proof for `Store` are very similar to that of `Load` so you should be able to figure this out from reading the proof above.

```coq
Lemma wp_HashMap__Store (hm_l: loc) γ (key: w32) (v: w64) P Q {Htimeless: ∀ m, Timeless (P m)} :
  {{{ is_hashmap γ hm_l P ∗
      (∀ m, P m -∗ |==> P (<[key := v]> m) ∗ Q m)
  }}}
    HashMap__Store #hm_l #key #v
  {{{ m0, RET #(); Q m0 }}}.
Proof.
Admitted.

End proof.
```
