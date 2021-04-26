Require Export Instances.Cat.Terminal.
Require Export Categories.Cone.
Require Export Categories.Comma.

Program Definition Comma2Cone {D C: Category} (F: Functor D C): Δ' ↓ @Δ _ 1 F ~> Cone F := {|
  fobj x := cone_nat (Comma.source x) (Comma.morph x);
  fmap x y f := {|
    Cone.mediator := Comma.smap f;
  |};
|}.
Next Obligation.
  rewrite <- comp_id_l.
  symmetry.
  change (Category.obj (Δ' ↓ @Δ _ 1 F)) in x, y.
  change ((fmap (Δ' F) (Comma.tmap f) ∘ Comma.morph x) x0 = (Comma.morph y ∘ ∇ (Comma.smap f)) x0).
  f_equal.
  apply Comma.comm.
Qed.
Next Obligation.
  now apply Cone.hom_eq.
Qed.
Next Obligation.
  now apply Cone.hom_eq.
Qed.

Program Definition Cone2Comma {D C: Category} (F: Functor D C): Functor (Cone F) (Δ' ↓ @Δ _ 1 F) := {|
  fobj x := {|
    Comma.source := Cone.vertex x;
    Comma.target := tt;
    Comma.morph := nat_cone x;
  |};
  fmap x y f := {|
    Comma.smap := Cone.mediator f;
    Comma.tmap := id tt;
  |};
|}.
Next Obligation.
  etransitivity.
  apply comp_id_l.
  symmetry.
  natural_eq a.
  apply Cone.mediator_comm.
Qed.
Next Obligation.
  now apply Comma.hom_eq.
Qed.
Next Obligation.
  now apply Comma.hom_eq.
Qed.

Lemma comma_cone_inv {D C: Category} (F: Functor D C): Comma2Cone F ∘ Cone2Comma F = id (Cone F).
Proof.
  fun_eq x y f.
  apply nat_cone_inv.
  Cone.hom_eq.
  destruct f as [f Hf].
  simpl; clear Hf.
  rewrite (is_eq_refl (Cone.mediator (to (eq_iso H)))).
  rewrite (is_eq_refl (Cone.mediator (to (eq_iso H0)))).
  simpl.
  rewrite comp_id_r.
  apply comp_id_l.
  1: apply (Cone.mediator_is_eq (to (eq_iso H0))).
  2: apply (Cone.mediator_is_eq (to (eq_iso H))).
  all: apply eq_iso_is_eq.
Qed.

Lemma cone_comma_inv {D C: Category} (F: Functor D C): Cone2Comma F ∘ Comma2Cone F = id (Δ' ↓ Δ F).
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

Canonical CommaCone {D C: Category} (F: Functor D C): Δ' ↓ @Δ _ 1 F <~> Cone F :=
  Isomorphism.Pack (Comma2Cone F) (Isomorphism.Mixin _ _ _ (Comma2Cone F) (Cone2Comma F) (cone_comma_inv F) (comma_cone_inv F)).

Program Definition Comma2Cocone {D C: Category} (F: Functor D C): @Δ _ 1 F ↓ Δ' ~> Cocone F := {|
  fobj x := cocone_nat (Comma.target x) (Comma.morph x);
  fmap x y f := {|
    Cocone.mediator := Comma.tmap f;
  |};
|}.
Next Obligation.
  rewrite <- comp_id_r.
  change (Category.obj (@Δ _ 1 F ↓ Δ')) in x, y.
  change ((∇ (Comma.tmap f) ∘ Comma.morph x) x0 = (Comma.morph y ∘ fmap (Δ F) (Comma.smap f)) x0).
  f_equal.
  apply Comma.comm.
Qed.
Next Obligation.
  now apply Cocone.hom_eq.
Qed.
Next Obligation.
  now apply Cocone.hom_eq.
Qed.

Program Definition Cocone2Comma {D C: Category} (F: Functor D C): Functor (Cocone F) (@Δ _ 1 F ↓ Δ') := {|
  fobj x := {|
    Comma.source := tt;
    Comma.target := Cocone.vertex x;
    Comma.morph := nat_cocone x;
  |};
  fmap x y f := {|
    Comma.smap := id tt;
    Comma.tmap := Cocone.mediator f;
  |};
|}.
Next Obligation.
  rewrite comp_id_r.
  natural_eq a.
  apply Cocone.mediator_comm.
Qed.
Next Obligation.
  now apply Comma.hom_eq.
Qed.
Next Obligation.
  now apply Comma.hom_eq.
Qed.

Lemma comma_cocone_inv {D C: Category} (F: Functor D C): Comma2Cocone F ∘ Cocone2Comma F = id (Cocone F).
Proof.
  fun_eq x y f.
  apply nat_cocone_inv.
  Cocone.hom_eq.
  destruct f as [f Hf].
  simpl; clear Hf.
  rewrite (is_eq_refl (Cocone.mediator (to (eq_iso H)))).
  rewrite (is_eq_refl (Cocone.mediator (to (eq_iso H0)))).
  simpl.
  rewrite comp_id_r.
  apply comp_id_l.
  1: apply (Cocone.mediator_is_eq (to (eq_iso H0))).
  2: apply (Cocone.mediator_is_eq (to (eq_iso H))).
  all: apply eq_iso_is_eq.
Qed.

Lemma cocone_comma_inv {D C: Category} (F: Functor D C): Cocone2Comma F ∘ Comma2Cocone F = id (Δ F ↓ Δ').
Proof.
  fun_eq x y f.
  destruct x, source.
  simpl.
  f_equal.
  apply cocone_nat_inv.
  apply Comma.hom_eq; simpl; split.
  apply unit_eq.
  revert H H0.
  rewrite !cocone_nat_inv.
  intros H H0.
  destruct x as [[] x x'], y as [[] y y'].
  rewrite !eq_iso_refl.
  simpl.
  clear H H0.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Canonical CommaCocone {D C: Category} (F: Functor D C): @Δ _ 1 F ↓ Δ' <~> Cocone F :=
  Isomorphism.Pack (Comma2Cocone F) (Isomorphism.Mixin _ _ _ (Comma2Cocone F) (Cocone2Comma F) (cocone_comma_inv F) (comma_cocone_inv F)).
