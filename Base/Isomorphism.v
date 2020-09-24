Require Export Categories.

Module Isomorphism.

Structure mixin_of {C: Category} {x y: C} (f: x ~> y) := Mixin {
  inv: y ~> x;
  inv_l: inv ∘ f = id x;
  inv_r: f ∘ inv = id y;
}.

Notation class_of := mixin_of (only parsing).

Section ClassDef.
Context {C: Category} {x y: C}.

Structure type := Pack { morphism: x ~> y; _: class_of morphism }.
Local Coercion morphism: type >-> hom.

Variable (i: type).
Definition class := match i return class_of i with Pack _ c => c end.

End ClassDef.

Module Exports.

Arguments type {_} _ _.
Coercion morphism: type >-> hom.
Notation to := morphism.
Notation iso := type.

End Exports.

End Isomorphism.

Export Isomorphism.Exports.

Section iso.
Context {C: Category} {x y: C} (i: iso x y).

Definition from: y ~> x := Isomorphism.inv i (Isomorphism.class i).

Lemma from_to: from ∘ i = id x.
Proof. apply Isomorphism.inv_l. Qed.
Lemma to_from: i ∘ from = id y.
Proof. apply Isomorphism.inv_r. Qed.

Definition inv_mixin: Isomorphism.mixin_of from :=
  Isomorphism.Mixin _ _ _ from i to_from from_to.

Global Canonical inv: iso y x :=
  Isomorphism.Pack from inv_mixin.

Lemma inv_l: inv ∘ i = id x.
Proof. apply Isomorphism.inv_l. Qed.

Lemma inv_r: i ∘ inv = id y.
Proof. apply Isomorphism.inv_r. Qed.

End iso.

Infix "<~>" := iso (at level 70, no associativity).
Notation "i '⁻¹'" := (inv i) (at level 9).

Definition id_iso_mixin {C: Category} (x: C): Isomorphism.mixin_of (id x) :=
  Isomorphism.Mixin C x x (id x) (id x) (comp_id_l (id x)) (comp_id_l (id x)).

Canonical id_iso {C: Category} (x: C): x <~> x :=
  Isomorphism.Pack (id x) (id_iso_mixin x).

Section Comp_iso.
Context {C: Category} {x y z: C} (i: y <~> z) (j: x <~> y).

Lemma comp_inv_l: j⁻¹ ∘ i⁻¹ ∘ (i ∘ j) = id x.
Proof.
  rewrite comp_assoc.
  rewrite <- (comp_assoc (j⁻¹)).
  rewrite inv_l, comp_id_r.
  apply inv_l.
Qed.

Lemma comp_inv_r: i ∘ j ∘ (j⁻¹ ∘ i⁻¹) = id z.
Proof.
  rewrite comp_assoc.
  rewrite <- (comp_assoc i).
  rewrite inv_r, comp_id_r.
  apply inv_r.
Qed.

Definition iso_comp_mixin: Isomorphism.mixin_of (i ∘ j) :=
  Isomorphism.Mixin _ _ _ (i ∘ j) (j⁻¹ ∘ i⁻¹) comp_inv_l comp_inv_r.

Global Canonical iso_comp: iso x z :=
  Isomorphism.Pack (i ∘ j) iso_comp_mixin.

End Comp_iso.

Infix "·" := iso_comp (at level 40, left associativity).

Lemma iso_eq {C: Category} {x y: C} (i j: x <~> y): i = j <-> to i = to j.
Proof.
  split; intro H.
  now subst j.
  destruct i as [f [f' Hf1 Hf2]], j as [g [g' Hg1 Hg2]].
  simpl in H.
  subst g.
  f_equal.
  enough (f' = g').
  subst g'.
  f_equal.
  1, 2: apply proof_irrelevance.
  rewrite <- (comp_id_r f').
  rewrite <- Hg2.
  rewrite comp_assoc.
  rewrite Hf1.
  apply comp_id_l.
Qed.

Lemma icomp_assoc {C: Category} {a b c d: C} (f: c <~> d) (g: b <~> c) (h: a <~> b): f · (g · h) = (f · g) · h.
Proof.
  apply iso_eq; simpl.
  apply comp_assoc.
Qed.

Lemma icomp_id_l {C: Category} {x y: C} (i: x <~> y): id_iso y · i = i.
Proof.
  apply iso_eq; simpl.
  apply comp_id_l.
Qed.

Lemma icomp_id_r {C: Category} {x y: C} (i: x <~> y): i · id_iso x = i.
Proof.
  apply iso_eq; simpl.
  apply comp_id_r.
Qed.

Lemma icomp_inv_l {C: Category} {x y: C} (i: x <~> y): i⁻¹ · i = id_iso x.
Proof.
  apply iso_eq; simpl.
  apply from_to.
Qed.

Lemma icomp_inv_r {C: Category} {x y: C} (i: x <~> y): i · i⁻¹ = id_iso y.
Proof.
  apply iso_eq; simpl.
  apply to_from.
Qed.

Definition isomorphic (C: Category) (X Y: C) := inhabited (X <~> Y).

Infix "≃" := (isomorphic _) (at level 70).

Instance isomorphic_equiv C: Equivalence (isomorphic C).
Proof.
  constructor.
  + intros x.
    constructor.
    exact (id_iso x).
  + intros x y H.
    destruct H as [i].
    constructor.
    exact (i⁻¹).
  + intros x y z H H0.
    destruct H as [i], H0 as [j].
    constructor.
    eapply iso_comp; eassumption.
Qed.

Definition eq_iso {C: Category} {X Y: C} (e: X = Y): X <~> Y :=
  match e in (_ = y) return (X <~> y) with
  | eq_refl => id_iso X
  end.

Theorem eq_iso_refl {C: Category} {X: C} (e: X = X): eq_iso e = id_iso X.
Proof.
  unfold eq_iso.
  assert (e = eq_refl).
  apply proof_irrelevance.
  subst e.
  reflexivity.
Qed.

Definition is_eq {C: Category} {X Y: C} (η: X ~> Y) :=
  exists e: X = Y, η = eq_iso e.

Lemma eq_iso_is_eq {C: Category} {X Y: C} (e: X = Y): is_eq (eq_iso e).
Proof. now exists e. Qed.

Lemma is_eq_refl {C: Category} {X: C} (η: X ~> X): is_eq η -> η = id X.
Proof.
  intros [e1 H1].
  subst η.
  now rewrite eq_iso_refl.
Qed.

Lemma is_eq_unique {C: Category} {X Y: C} (η ϵ: X ~> Y): is_eq η -> is_eq ϵ -> η = ϵ.
Proof.
  intros [e1 H1] [e2 H2].
  subst η ϵ.
  do 2 f_equal.
  apply proof_irrelevance.
Qed.

Lemma is_eq_unique_iso {C: Category} {X Y: C} (η ϵ: X <~> Y): is_eq η -> is_eq ϵ -> η = ϵ.
Proof.
  intros Hη Hϵ.
  now apply iso_eq, is_eq_unique.
Qed.

Lemma is_eq_id {C: Category} {X: C}: is_eq (id X).
Proof. now exists eq_refl. Qed.

Lemma is_eq_comp {C: Category} {X Y Z: C} (ϵ: Y ~> Z) (η: X ~> Y): is_eq η -> is_eq ϵ -> is_eq (ϵ ∘ η).
Proof.
  intros [e1 H1] [e2 H2].
  subst η ϵ Y Z.
  simpl.
  rewrite comp_id_l.
  apply is_eq_id.
Qed.

Lemma is_eq_inv {C: Category} {X Y: C} (η: X <~> Y): is_eq η -> is_eq η⁻¹.
Proof.
  intros [e H].
  apply iso_eq in H.
  subst η Y.
  apply is_eq_id.
Qed.

Theorem iso_monic {C: Category} {x y: C} (i: x <~> y): monic i.
Proof.
  intros z f g H.
  rewrite <- (comp_id_l f), <- (comp_id_l g).
  rewrite <- (inv_l i).
  rewrite <- !comp_assoc.
  now f_equal.
Qed.

Theorem iso_epic {C: Category} {x y: C} (i: x <~> y): epic i.
Proof.
  intros z f g H.
  rewrite <- (comp_id_r f), <- (comp_id_r g).
  rewrite <- (inv_r i).
  rewrite !comp_assoc.
  now f_equal.
Qed.

Definition co_iso_mixin {C: Category} {x y: C} (i: x <~> y): Isomorphism.mixin_of (from i: @hom (co C) x y) :=
  Isomorphism.Mixin (co C) x y (from i) (to i) (from_to i) (to_from i).

Definition co_iso {C: Category} {x y: C} (i: x <~> y): (x: co C) <~> y :=
  Isomorphism.Pack _ (co_iso_mixin i).

Definition co_iso_mixin' {C: Category} {x y: C} (i: (x: co C) <~> y): Isomorphism.mixin_of (from i: x ~> y) :=
  Isomorphism.Mixin C x y (from i) (to i) (from_to i) (to_from i).

Definition co_iso' {C: Category} {x y: C} (i: (x: co C) <~> y): x <~> y :=
  Isomorphism.Pack _ (co_iso_mixin' i).

Theorem iso_co {C: Category} (x y: C): (x: co C) ≃ y <-> x ≃ y.
  split.
  + intros [i].
    constructor.
    apply co_iso', i.
  + intros [i].
    constructor.
    apply co_iso, i.
Qed.

Lemma is_eq_co {C: Category} {x y: C} (f: x ~> y): is_eq f -> is_eq (f: (y: co C) ~> x).
Proof.
  intros [e H].
  subst f y.
  exact is_eq_id.
Qed.
