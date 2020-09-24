Require Export Cat.
Require Export Cone.
Require Export Comma.

Program Definition Comma2Cone {D C: Category} (F: D ~> C): Δ ↓ @Δ _ 1 F ~> Cones F := {|
  fobj x := cone_nat (Comma.source x) (Comma.morph x);
  fmap x y f := {|
    mediator := Comma.smap f;
  |};
|}.
Next Obligation.
  rewrite <- comp_id_l.
  symmetry.
  change (Category.obj (Δ ↓ @Δ _ 1 F)) in x, y.
  change ((fmap (Δ F) (Comma.tmap f) ∘ Comma.morph x) x0 = (Comma.morph y ∘ fmap Δ (Comma.smap f)) x0).
  f_equal.
  apply Comma.comm.
Qed.
Next Obligation.
  now apply conemor_eq.
Qed.
Next Obligation.
  now apply conemor_eq.
Qed.

Program Definition Cone2Comma {D C: Category} (F: D ~> C): Cones F ~> Δ ↓ @Δ _ 1 F := {|
  fobj x := {|
    Comma.source := vertex x;
    Comma.target := tt;
    Comma.morph := nat_cone x;
  |};
  fmap x y f := {|
    Comma.smap := mediator f;
    Comma.tmap := id tt;
  |};
|}.
Next Obligation.
  etransitivity.
  apply comp_id_l.
  symmetry.
  natural_eq a.
  apply mediator_comm.
Qed.
Next Obligation.
  now apply Comma.hom_eq.
Qed.
Next Obligation.
  now apply Comma.hom_eq.
Qed.

Lemma comma_cone_inv {D C: Category} (F: D ~> C): Comma2Cone F ∘ Cone2Comma F = id (Cones F).
Proof.
  fun_eq x y f.
  apply nat_cone_inv.
  conemor_eq.
  destruct f as [f Hf].
  simpl; clear Hf.
  enough (is_eq (mediator (to (eq_iso H)))) as [e1 H1].
  enough (is_eq (mediator (to (eq_iso H0)))) as [e2 H2].
  rewrite H1, H2; clear H H0 H1 H2.
  rewrite !eq_iso_refl.
  simpl.
  clear e1 e2.
  rewrite comp_id_r.
  apply comp_id_l.
  all: apply mediator_is_eq, eq_iso_is_eq.
Qed.

Lemma cone_comma_inv {D C: Category} (F: D ~> C): Cone2Comma F ∘ Comma2Cone F = id (Δ ↓ Δ F).
Proof.
  fun_eq x y f.
  destruct x, target.
  simpl.
  f_equal.
  apply cone_nat_inv.
  apply Comma.hom_eq; simpl; split.
  revert H H0.
  rewrite !cone_nat_inv.
  intros H H0.
  destruct x as [x [] x'], y as [y [] y'].
  rewrite !eq_iso_refl.
  simpl.
  clear H H0.
  rewrite comp_id_r.
  apply comp_id_l.
  apply unit_eq.
Qed.

Canonical CommaCone {D C: Category} (F: D ~> C): Δ ↓ @Δ _ 1 F <~> Cones F :=
  Isomorphism.Pack (Comma2Cone F) (Isomorphism.Mixin _ _ _ (Comma2Cone F) (Cone2Comma F) (cone_comma_inv F) (comma_cone_inv F)).

Program Definition Comma2Cocone {D C: Category} (F: D ~> C): @Δ _ 1 F ↓ Δ ~> co (Cones (cof F)) := {|
  fobj (x: @Δ _ 1 F ↓ Δ) := {|
    vertex := Comma.target x;
    edge := Comma.morph x;
  |};
  fmap x y f := {|
    mediator := Comma.tmap f;
  |};
|}.
Next Obligation.
  change (Comma.morph x x0 ∘ fmap F f = Comma.morph x y).
  rewrite <- comp_id_l.
  simpl.
  apply (naturality (Comma.morph x)).
Qed.
Next Obligation.
  change (Comma.tmap f ∘ Comma.morph x x0 = Comma.morph y x0).
  rewrite <- comp_id_r.
  simpl.
  change ((fmap Δ (Comma.tmap f) ∘ Comma.morph x) x0 = (Comma.morph y ∘ fmap (Δ F) (Comma.smap f)) x0).
  f_equal.
  apply Comma.comm.
Qed.
Next Obligation.
  now apply conemor_eq.
Qed.
Next Obligation.
  now apply conemor_eq.
Qed.

Program Definition Cocone2Comma {D C: Category} (F: D ~> C): co (Cones (cof F)) ~> @Δ _ 1 F ↓ Δ := {|
  fobj x := {|
    Comma.source := tt;
    Comma.target := vertex x;
    Comma.morph := {|
      transform := edge x;
    |};
  |};
  fmap x y f := {|
    Comma.smap := id tt;
    Comma.tmap := mediator f;
  |};
|}.
Next Obligation.
  rewrite comp_id_l.
  apply (edge_comm x).
Qed.
Next Obligation.
  natural_eq i.
  rewrite comp_id_r.
  apply (mediator_comm f).
Qed.
Next Obligation.
  now apply Comma.hom_eq.
Qed.
Next Obligation.
  now apply Comma.hom_eq.
Qed.

Lemma comma_cocone_inv {D C: Category} (F: D ~> C): Comma2Cocone F ∘ Cocone2Comma F = id (co (Cones (cof F))).
Proof.
  fun_eq x y f.
  destruct x; simpl.
  f_equal.
  apply proof_irrelevance.
  conemor_eq.
  etransitivity.
  apply f_equal.
  apply is_eq_refl.
  destruct H0.
  apply is_eq_id.
  rewrite comp_id_r.
  rewrite <- (comp_id_l (mediator f)) at 1.
  f_equal.
  symmetry.
  apply is_eq_refl.
  destruct H.
  apply is_eq_id.
Qed.

Lemma cocone_comma_inv {D C: Category} (F: D ~> C): Cocone2Comma F ∘ Comma2Cocone F = id (Δ F ↓ Δ).
Proof.
  fun_eq x y f.
  destruct x, source, morph.
  simpl.
  do 2 f_equal.
  apply proof_irrelevance.
  apply Comma.hom_eq; simpl; split.
  apply unit_eq.
  etransitivity.
  apply (f_equal (fun f => f ∘ _)).
  apply is_eq_refl.
  destruct H0.
  exact is_eq_id.
  symmetry.
  etransitivity.
  apply f_equal.
  apply is_eq_refl.
  destruct H.
  apply is_eq_id.
  rewrite comp_id_l.
  apply comp_id_r.
Qed.

Canonical CommaCocone {D C: Category} (F: D ~> C): @Δ _ 1 F ↓ Δ <~> co (Cones (cof F)) :=
  Isomorphism.Pack (Comma2Cocone F) (Isomorphism.Mixin _ _ _ (Comma2Cocone F) (Cocone2Comma F) (cocone_comma_inv F) (comma_cocone_inv F)).
