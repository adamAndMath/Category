Require Export Natural.

Definition adjoint_by {C D: Category} (F: D ~> C) (G: C ~> D) (ɛ: F ∘ G ~> id C) (η: id D ~> G ∘ F) :=
  (ɛ |> F) ∘ α F G F ∘ (F <| η) = (ρ F)⁻¹ ∘ λ F /\
  (G <| ɛ) ∘ (α G F G)⁻¹ ∘ (η |> G) = (ρ G)⁻¹ ∘ λ G.

Lemma adjoint_by_alt {C D: Category} (F: D ~> C) (G: C ~> D) (ɛ: F ∘ G ~> id C) (η: id D ~> G ∘ F):
  adjoint_by F G ɛ η <->
  (forall x, ɛ (F x) ∘ fmap F (η x) = id (F x)) /\
  (forall x, fmap G (ɛ x) ∘ η (G x) = id (G x)).
Proof.
  unfold adjoint_by.
  f_equiv.
  all: etransitivity.
  1, 3: apply natural_eq.
  all: simpl.
  all: change (from ?i) with (to i⁻¹).
  all: split.
  all: intros H x.
  all: specialize (H x).
  + rewrite (is_eq_refl (to (α F G F) x)), comp_id_r in H.
    rewrite H.
    apply is_eq_refl.
    apply is_eq_comp.
    apply (transform_is_eq (λ F)), unitor_l_is_eq.
    apply (transform_is_eq (ρ F)⁻¹), is_eq_inv, unitor_r_is_eq.
    apply (transform_is_eq (α F G F)), associator_is_eq.
  + rewrite (is_eq_refl (to (α F G F) x)), comp_id_r.
    rewrite H.
    symmetry.
    apply is_eq_refl.
    apply is_eq_comp.
    apply (transform_is_eq (λ F)), unitor_l_is_eq.
    apply (transform_is_eq (ρ F)⁻¹), is_eq_inv, unitor_r_is_eq.
    apply (transform_is_eq (α F G F)), associator_is_eq.
  + rewrite (is_eq_refl (to (α G F G)⁻¹ x)), comp_id_r in H.
    rewrite H.
    apply is_eq_refl.
    apply is_eq_comp.
    apply (transform_is_eq (λ G)), unitor_l_is_eq.
    apply (transform_is_eq (ρ G)⁻¹), is_eq_inv, unitor_r_is_eq.
    apply (transform_is_eq (α G F G)⁻¹), is_eq_inv, associator_is_eq.
  + rewrite (is_eq_refl (to (α G F G)⁻¹ x)), comp_id_r.
    rewrite H.
    symmetry.
    apply is_eq_refl.
    apply is_eq_comp.
    apply (transform_is_eq (λ G)), unitor_l_is_eq.
    apply (transform_is_eq (ρ G)⁻¹), is_eq_inv, unitor_r_is_eq.
    apply (transform_is_eq (α G F G)⁻¹), is_eq_inv, associator_is_eq.
Qed.

Definition adjoint {C D: Category} (F: D ~> C) (G: C ~> D) :=
  exists ɛ η, adjoint_by F G ɛ η.

Infix "-|" := adjoint (at level 60, no associativity).

Lemma iso_adjoint {C D: Category} (I: C <~> D): I -| I⁻¹.
Proof.
  red.
  exists (to (eq_iso (inv_r I))), (to (eq_iso (inv_l I))⁻¹).
  apply adjoint_by_alt.
  split; intros x.
  all: apply is_eq_refl.
  all: apply is_eq_comp.
  1: apply (fmap_is_eq I).
  4: apply (fmap_is_eq I⁻¹).
  1, 3: apply (transform_is_eq (eq_iso (inv_l I))⁻¹).
  3, 4: apply (transform_is_eq (eq_iso (inv_r I))).
  1, 2: apply is_eq_inv.
  all: apply eq_iso_is_eq.
Qed.

Lemma adjoint_comp {A B C: Category} (F: C ~> B) (G: B ~> C) (F': B ~> A) (G': A ~> B): F -| G -> F' -| G' -> F' ∘ F -| G ∘ G'.
Proof.
  intros [ɛ [η adj]] [ɛ' [η' adj']].
  exists (ɛ' ∘ ((ρ F' ∘ (F' <| ɛ) ∘ (α F' F G)⁻¹) |> G') ∘ α (F' ∘ F) G G').
  exists ((α (G ∘ G') F' F)⁻¹ ∘ ((α G G' F' ∘ (G <| η') ∘ (ρ G)⁻¹) |> F) ∘ η).
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
    rewrite (is_eq_refl (to (ρ F') (G' (F' (F x))))), comp_id_l.
    rewrite (is_eq_refl (from (α F' F G) (G' (F' (F x))))), comp_id_r.
    rewrite (is_eq_refl (to (α (F' ∘ F) G G') (F' (F x)))), comp_id_r.
    rewrite (is_eq_refl (from (α (G ∘ G') F' F) x)), comp_id_l.
    rewrite (is_eq_refl (to (α G G' F') (F x))), comp_id_l.
    rewrite (is_eq_refl (from (ρ G) (F x))), comp_id_r.
    rewrite <- adj'.
    rewrite <- comp_assoc.
    f_equiv.
    rewrite <- fmap_comp.
    f_equiv.
    rewrite fmap_comp, comp_assoc.
    change (ɛ ((G' ∘ F') (F x)) ∘ fmap (F ∘ G) (η' (F x)) ∘ fmap F (η x) = η' (F x)).
    rewrite (naturality ɛ (η' (F x))).
    rewrite <- comp_assoc.
    rewrite adj.
    apply comp_id_r.
    all: change (from ?i) with (to i⁻¹).
    apply (transform_is_eq (ρ G)⁻¹), is_eq_inv, unitor_r_is_eq.
    apply (transform_is_eq (α G G' F')), associator_is_eq.
    apply (transform_is_eq (α (G ∘ G') F' F)⁻¹), is_eq_inv, associator_is_eq.
    apply (transform_is_eq (α (F' ∘ F) G G')), associator_is_eq.
    apply (transform_is_eq (α F' F G)⁻¹), is_eq_inv, associator_is_eq.
    apply (transform_is_eq (ρ F')), unitor_r_is_eq.
  + intros x.
    simpl.
    rewrite (is_eq_refl (to (ρ F') (G' x))), comp_id_l.
    rewrite (is_eq_refl (from (α F' F G) (G' x))), comp_id_r.
    rewrite (is_eq_refl (to (α (F' ∘ F) G G') x)), comp_id_r.
    rewrite (is_eq_refl (from (α (G ∘ G') F' F) (G (G' x)))), comp_id_l.
    rewrite (is_eq_refl (to (α G G' F') (F (G (G' x))))), comp_id_l.
    rewrite (is_eq_refl (from (ρ G) (F (G (G' x))))), comp_id_r.
    rewrite <- adj.
    rewrite comp_assoc.
    f_equiv.
    rewrite <- fmap_comp.
    f_equiv.
    rewrite fmap_comp, <- comp_assoc.
    change (fmap G' (ɛ' x) ∘ (fmap (G' ∘ F') (ɛ (G' x)) ∘ η' ((F ∘ G) (G' x))) = ɛ (G' x)).
    rewrite <- naturality.
    rewrite comp_assoc.
    simpl.
    etransitivity.
    apply (f_equal (fun f => f ∘ _)).
    exact (adj' x).
    apply comp_id_l.
    all: change (from ?i) with (to i⁻¹).
    apply (transform_is_eq (ρ G)⁻¹), is_eq_inv, unitor_r_is_eq.
    apply (transform_is_eq (α G G' F')), associator_is_eq.
    apply (transform_is_eq (α (G ∘ G') F' F)⁻¹), is_eq_inv, associator_is_eq.
    apply (transform_is_eq (α (F' ∘ F) G G')), associator_is_eq.
    apply (transform_is_eq (α F' F G)⁻¹), is_eq_inv, associator_is_eq.
    apply (transform_is_eq (ρ F')), unitor_r_is_eq.
Qed.

Instance adjoint_iso (C D: Category): Proper (isomorphic (Fun D C) ==> isomorphic (Fun C D) ==> iff) adjoint.
Proof.
  enough (Proper (isomorphic (Fun D C) ==> isomorphic (Fun C D) ==> impl) adjoint).
  now split; apply H.
  intros F F' I G G' J.
  transitivity (F' -| G).
  1: clear G' J; destruct I as [I].
  2: clear F I; rename F' into F; destruct J as [I].
  + intros [ɛ [η adj]].
    exists (ɛ ∘ (I⁻¹ |> G)), ((G <| I) ∘ η).
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
  + intros [ɛ [η adj]].
    exists (ɛ ∘ (F <| I⁻¹)), ((I |> F) ∘ η).
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
