Require Export Base.Equivalence.

Definition adjoint_by {C D: Category} (F: D ~> C) (G: C ~> D) (η: id D ~> G ∘ F) (ɛ: F ∘ G ~> id C) :=
  (ɛ |> F) ∘ α F G F ∘ (F <| η) = (ρ F)⁻¹ ∘ λ F /\
  (G <| ɛ) ∘ (α G F G)⁻¹ ∘ (η |> G) = (ρ G)⁻¹ ∘ λ G.

Lemma adjoint_by_alt {C D: Category} (F: D ~> C) (G: C ~> D) (η: id D ~> G ∘ F) (ɛ: F ∘ G ~> id C):
  adjoint_by F G η ɛ <->
  (forall x, ɛ (F x) ∘ fmap F (η x) = id (F x)) /\
  (forall x, fmap G (ɛ x) ∘ η (G x) = id (G x)).
Proof.
  unfold adjoint_by.
  f_equiv.
  all: etransitivity.
  1, 3: apply natural_eq.
  all: simpl.
  all: split.
  all: intros H x.
  all: specialize (H x).
  1, 3: rewrite !comp_id_r in H.
  3, 4: rewrite !comp_id_r.
  all: exact H.
Qed.

Definition adjoint {C D: Category} (F: D ~> C) (G: C ~> D) :=
  exists η ɛ, adjoint_by F G η ɛ.

Infix "-|" := adjoint (at level 60, no associativity).

Lemma iso2_adjoint {C D: Category} (I: C <=> D): I -| I⁻.
Proof.
  red.
  exists (to (iunit I)⁻¹), (to (icounit I)).
  apply adjoint_by_alt.
  split; intros x.
  rewrite <- (iunit_to I).
  etransitivity.
  symmetry.
  apply (@fmap_comp _ _ I).
  rewrite <- fmap_id.
  f_equal.
  change ((iunit I ∘ (iunit I)⁻¹) x = id (id C) x).
  f_equal.
  apply inv_r.
  simpl.
  etransitivity.
  apply (f_equal (fun f => f ∘ _)).
  apply iunit_from.
  change ((iunit I ∘ (iunit I)⁻¹) (I⁻ x) = id (id C) (I⁻ x)).
  f_equal.
  apply inv_r.
Qed.

Lemma iso_adjoint {C D: Category} (I: C <~> D): I -| I⁻¹.
Proof. apply (iso2_adjoint (iso_iso2 _ _ I)). Qed.

Lemma adjoint_comp {A B C: Category} (F: C ~> B) (G: B ~> C) (F': B ~> A) (G': A ~> B): F -| G -> F' -| G' -> F' ∘ F -| G ∘ G'.
Proof.
  intros [η [ɛ adj]] [η' [ɛ' adj']].
  exists ((α (G ∘ G') F' F)⁻¹ ∘ ((α G G' F' ∘ (G <| η') ∘ (ρ G)⁻¹) |> F) ∘ η).
  exists (ɛ' ∘ ((ρ F' ∘ (F' <| ɛ) ∘ (α F' F G)⁻¹) |> G') ∘ α (F' ∘ F) G G').
  apply adjoint_by_alt in adj.
  apply adjoint_by_alt in adj'.
  apply adjoint_by_alt.
  split; [
    apply proj1 in adj;
    apply proj1 in adj'
  | apply proj2 in adj;
    apply proj2 in adj'
  ].
  + intros x.
    simpl.
    rewrite !comp_id_l, !comp_id_r.
    rewrite <- adj'.
    rewrite <- comp_assoc.
    f_equal.
    rewrite <- fmap_comp.
    f_equal.
    rewrite fmap_comp, comp_assoc.
    change (ɛ ((G' ∘ F') (F x)) ∘ fmap (F ∘ G) (η' (F x)) ∘ fmap F (η x) = η' (F x)).
    rewrite (naturality ɛ (η' (F x))).
    rewrite <- comp_assoc.
    rewrite adj.
    apply comp_id_r.
  + intros x.
    simpl.
    rewrite !comp_id_l, !comp_id_r.
    rewrite <- adj.
    rewrite comp_assoc.
    f_equal.
    rewrite <- fmap_comp.
    f_equal.
    rewrite fmap_comp, <- comp_assoc.
    change (fmap G' (ɛ' x) ∘ (fmap (G' ∘ F') (ɛ (G' x)) ∘ η' ((F ∘ G) (G' x))) = ɛ (G' x)).
    rewrite <- naturality.
    rewrite comp_assoc.
    simpl.
    etransitivity.
    apply (f_equal (fun f => f ∘ _)).
    exact (adj' x).
    apply comp_id_l.
Qed.

Lemma adjoint_comp_iso_l {A B C: Category} (I: B <~> C) (F: B ~> A) (G: A ~> B): F ∘ I⁻¹ -| I ∘ G <-> F -| G.
Proof.
  split.
  2: apply adjoint_comp, iso_adjoint.
  intros H.
  rewrite <- (comp_id_r F), <- comp_id_l.
  rewrite <- (inv_l I).
  rewrite <- comp_assoc, comp_assoc.
  apply adjoint_comp, H.
  apply iso_adjoint.
Qed.

Lemma adjoint_comp_iso_r {A B C: Category} (F: C ~> B) (G: B ~> C) (I: A <~> B): I⁻¹ ∘ F -| G ∘ I <-> F -| G.
Proof.
  split.
  all: intros H.
  rewrite <- (comp_id_l F), <- comp_id_r.
  rewrite <- (inv_r I).
  rewrite comp_assoc, <- comp_assoc.
  all: apply adjoint_comp.
  1, 3: exact H.
  all: apply iso_adjoint.
Qed.

Instance adjoint_iso (C D: Category): Proper (isomorphic (Fun D C) ==> isomorphic (Fun C D) ==> iff) adjoint.
Proof.
  enough (Proper (isomorphic (Fun D C) ==> isomorphic (Fun C D) ==> impl) adjoint).
  now split; apply H.
  intros F F' I G G' J.
  transitivity (F' -| G).
  1: clear G' J; destruct I as [I].
  2: clear F I; rename F' into F; destruct J as [I].
  + intros [η [ɛ adj]].
    exists ((G <| I) ∘ η), (ɛ ∘ (I⁻¹ |> G)).
    apply adjoint_by_alt in adj.
    apply adjoint_by_alt.
    split; [apply proj1 in adj | apply proj2 in adj].
    - intros x.
      simpl.
      change (from I) with (to I⁻¹).
      rewrite <- comp_assoc.
      rewrite naturality.
      rewrite comp_assoc.
      rewrite fmap_comp.
      rewrite comp_assoc.
      change (fmap F (fmap G (to I x))) with (fmap (F ∘ G) (to I x)).
      setoid_rewrite (naturality ɛ (to I x)).
      rewrite <- (comp_assoc _ (ɛ (F x))).
      setoid_rewrite adj.
      rewrite comp_id_r.
      change ((I ∘ I⁻¹) x = id F' x).
      f_equal.
      apply inv_r.
    - intros x.
      simpl.
      change (from I) with (to I⁻¹).
      rewrite comp_assoc.
      rewrite <- fmap_comp.
      rewrite <- comp_assoc.
      change (to I⁻¹ (G x) ∘ to I (G x)) with ((I⁻¹ ∘ I) (G x)).
      rewrite inv_l.
      simpl.
      rewrite comp_id_r.
      apply adj.
  + intros [η [ɛ adj]].
    exists ((I |> F) ∘ η), (ɛ ∘ (F <| I⁻¹)).
    apply adjoint_by_alt in adj.
    apply adjoint_by_alt.
    split; [apply proj1 in adj | apply proj2 in adj].
    - intros x.
      simpl.
      change (from I) with (to I⁻¹).
      rewrite <- comp_assoc.
      rewrite <- fmap_comp.
      rewrite comp_assoc.
      change (to I⁻¹ (F x) ∘ to I (F x)) with ((I⁻¹ ∘ I) (F x)).
      rewrite inv_l.
      simpl.
      rewrite comp_id_l.
      apply adj.
    - intros x.
      simpl.
      change (from I) with (to I⁻¹).
      rewrite comp_assoc.
      rewrite <- naturality.
      rewrite <- comp_assoc.
      rewrite fmap_comp.
      rewrite <- comp_assoc.
      change (fmap G (fmap F (to I⁻¹ x))) with (fmap (G ∘ F) (to I⁻¹ x)).
      setoid_rewrite <- (naturality η (to I⁻¹ x)).
      rewrite (comp_assoc (fmap G (ɛ x))).
      rewrite adj, comp_id_l.
      change ((I ∘ I⁻¹) x = id G' x).
      f_equal.
      apply inv_r.
Qed.

Lemma adjoint_co {C D: Category} (F: D ~> C) (G: C ~> D): F -| G <-> to (CoFun C D) G -| to (CoFun D C) F.
Proof.
  split.
  intros [η [ɛ adj]].
  exists (fmap (to (CoFun C C)) ɛ), (fmap (to (CoFun D D)) η).
  apply adjoint_by_alt in adj.
  apply adjoint_by_alt.
  easy.
  revert C D F G.
  enough (forall C D (F: co D ~> co C) (G: co C ~> co D), F -| G -> to (CoFun C D)⁻¹ G -| to (CoFun D C)⁻¹ F).
  all: intros C D F G.
  intros adj.
  apply H in adj.
  simpl in adj.
  rewrite !cof_inv_l in adj.
  exact adj.
  intros [η [ɛ adj]].
  exists (fmap (to (CoFun C C)⁻¹) ɛ), (fmap (to (CoFun D D)⁻¹) η).
  apply adjoint_by_alt in adj.
  apply adjoint_by_alt.
  easy.
Qed.

Lemma left_adjoint_unique {C D: Category} (F1 F2: D ~> C) (G: C ~> D): F1 -| G -> F2 -| G -> F1 ≃ F2.
Proof.
  intros [η1 [ɛ1 H1]] [η2 [ɛ2 H2]].
  rewrite adjoint_by_alt in H1, H2.
  constructor.
  exists (λ F2 ∘ (ɛ1 |> F2) ∘ α F1 G F2 ∘ (F1 <| η2) ∘ (ρ F1)⁻¹).
  exists (λ F1 ∘ (ɛ2 |> F1) ∘ α F2 G F1 ∘ (F2 <| η1) ∘ (ρ F2)⁻¹).
  all: natural_eq x.
  all: rewrite !comp_id_l, !comp_id_r.
  all: rewrite comp_assoc.
  all: change (?f ∘ ?g ∘ ?h = ?i) with (fmap (id C) f ∘ g ∘ h = i).
  all: rewrite <- naturality.
  all: simpl.
  all: rewrite <- comp_assoc.
  all: rewrite fmap_comp, <- fmap_comp.
  all: rewrite <- comp_assoc.
  all: change (fmap ?F (fmap ?G ?f) ∘ ?η x) with (fmap (F ∘ G) f ∘ η (id D x)).
  all: rewrite <- naturality.
  all: simpl.
  all: rewrite comp_assoc.
  1: setoid_rewrite (proj2 H2).
  2: setoid_rewrite (proj2 H1).
  all: rewrite comp_id_l.
  apply H1.
  apply H2.
Qed.

Lemma right_adjoint_unique {C D: Category} (F: D ~> C) (G1 G2: C ~> D): F -| G1 -> F -| G2 -> G1 ≃ G2.
Proof.
  intros [η1 [ɛ1 H1]] [η2 [ɛ2 H2]].
  rewrite adjoint_by_alt in H1, H2.
  constructor.
  exists (ρ G2 ∘ (G2 <| ɛ1) ∘ (α G2 F G1)⁻¹ ∘ (η2 |> G1) ∘ (λ G1)⁻¹).
  exists (ρ G1 ∘ (G1 <| ɛ2) ∘ (α G1 F G2)⁻¹ ∘ (η1 |> G2) ∘ (λ G2)⁻¹).
  all: natural_eq x.
  all: rewrite !comp_id_l, !comp_id_r.
  all: rewrite <- comp_assoc.
  all: change (?f ∘ (?g ∘ ?h) = ?i) with (f ∘ (g ∘ fmap (id D) h) = i).
  all: rewrite naturality.
  all: simpl.
  all: rewrite comp_assoc.
  all: rewrite fmap_comp, <- fmap_comp.
  all: rewrite comp_assoc.
  all: change (?η x ∘ fmap ?F (fmap ?G ?f)) with (η (id C x) ∘ fmap (F ∘ G) f).
  all: rewrite naturality.
  all: simpl.
  all: rewrite <- comp_assoc.
  1: setoid_rewrite (proj1 H2 (G1 x)).
  2: setoid_rewrite (proj1 H1 (G2 x)).
  all: rewrite comp_id_r.
  apply H1.
  apply H2.
Qed.
