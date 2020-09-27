Require Export Base.

Module Typ.
Definition id A: A -> A := fun a => a.

Definition comp {A B C} (g: B -> C) (f: A -> B): A -> C :=
  fun a => g (f a).

Lemma comp_assoc {A B C D} (h: C -> D) (g: B -> C) (f: A -> B): comp h (comp g f) = comp (comp h g) f.
Proof. now extensionality a. Qed.

Lemma comp_id_l {A B} (f: A -> B): comp (id B) f = f.
Proof. now extensionality a. Qed.

Lemma comp_id_r {A B} (f: A -> B): comp f (id A) = f.
Proof. now extensionality a. Qed.

Definition cat_mixin: Category.mixin_of Type :=
  Category.Mixin Type (fun A B => A -> B) id (@comp) (@comp_assoc) (@comp_id_l) (@comp_id_r).

Canonical cat: Category :=
  Category.Pack Type cat_mixin.
End Typ.

Canonical Typ.cat.
Notation Typ := Typ.cat.

Require Import Cat.

Program Definition Hom (C: Category): co C × C ~> Typ := {|
  fobj (p: co C × C) := (fst p: C) ~> snd p;
  fmap _ _ f x := snd f ∘ x ∘ fst f;
|}.
Next Obligation.
  extensionality f.
  simpl.
  rewrite (comp_id_r (_ ∘ f)).
  apply comp_id_l.
Qed.
Next Obligation.
  rename o3 into A1, o4 into A2, o1 into B1, o2 into B2, o into C1, o0 into C2.
  extensionality x.
  unfold comp at 4 5; simpl.
  unfold Typ.comp.
  rewrite !comp_assoc.
  apply comp_assoc.
Qed.

Section Adjoint2hom.
Context {C D: Category} (F: C ~> D) (G: D ~> C) ɛ η (adj: adjoint_by F G ɛ η).

Program Definition adjoint_hom_iso_to: Hom D ∘ ⟨cof F ∘ π₁, π₂⟩ ~> Hom C ∘ ⟨π₁, G ∘ π₂⟩ := {|
  transform x f := fmap G f ∘ η (fst x);
|}.
Next Obligation.
  unfold comp at 1 6; simpl.
  unfold Typ.comp.
  extensionality g.
  rewrite comp_assoc, <- fmap_comp.
  rewrite fmap_comp.
  rewrite <- !comp_assoc.
  f_equal.
  symmetry.
  apply (naturality η).
Qed.

Program Definition adjoint_hom_iso_from: Hom C ∘ ⟨π₁, G ∘ π₂⟩ ~> Hom D ∘ ⟨cof F ∘ π₁, π₂⟩ := {|
  transform x f := ɛ (snd x) ∘ fmap F f;
|}.
Next Obligation.
  unfold comp at 1 6; simpl.
  unfold Typ.comp.
  extensionality g.
  rewrite comp_assoc, <- comp_assoc, <- comp_assoc.
  rewrite <- fmap_comp, fmap_comp.
  rewrite comp_assoc.
  apply (f_equal (fun f => f ∘ _)).
  apply (naturality ɛ).
Qed.

Lemma adjoint_hom_iso_inv_l: adjoint_hom_iso_from ∘ adjoint_hom_iso_to = id _.
Proof.
  apply adjoint_by_alt in adj.
  natural_eq p.
  unfold comp at 1; simpl.
  unfold id; simpl.
  unfold Typ.comp, Typ.id.
  extensionality f.
  rewrite fmap_comp.
  rewrite comp_assoc.
  etransitivity.
  apply (f_equal (fun f => f ∘ _)).
  apply (naturality ɛ).
  simpl.
  rewrite <- comp_assoc.
  rewrite <- (comp_id_r f) at 2.
  apply f_equal.
  apply adj.
Qed.

Lemma adjoint_hom_iso_inv_r: adjoint_hom_iso_to ∘ adjoint_hom_iso_from = id _.
Proof.
  apply adjoint_by_alt in adj.
  natural_eq p.
  unfold comp at 1; simpl.
  unfold id; simpl.
  unfold Typ.comp, Typ.id.
  extensionality f.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  etransitivity.
  apply f_equal.
  symmetry.
  apply (naturality η).
  simpl.
  rewrite comp_assoc.
  rewrite <- (comp_id_l f) at 2.
  f_equal.
  apply adj.
Qed.

Definition adjoint_hom_iso: Hom D ∘ ⟨cof F ∘ π₁, π₂⟩ <~> Hom C ∘ ⟨π₁, G ∘ π₂⟩ :=
  Isomorphism.Pack adjoint_hom_iso_to (Isomorphism.Mixin _ _ _ adjoint_hom_iso_to adjoint_hom_iso_from adjoint_hom_iso_inv_l adjoint_hom_iso_inv_r).

End Adjoint2hom.

Section Hom2Adjoint.
Context {C D: Category} (F: C ~> D) (G: D ~> C) (i: Hom D ∘ ⟨cof F ∘ π₁, π₂⟩ <~> Hom C ∘ ⟨π₁, G ∘ π₂⟩).

Program Definition hom_unit: id C ~> G ∘ F := {|
  transform x := (to i (x, F x) (id (F x)));
|}.
Next Obligation.
  generalize (naturality (to i) ((id (x: co C), fmap F f): (_, _) ~> (_, _))).
  intros H.
  specialize (f_equal (fun f => f (id (F x))) H).
  clear H; intros H.
  simpl in H.
  unfold comp at 1 12 in H; simpl in H.
  unfold Typ.comp in H.
  rewrite comp_id_r in H.
  setoid_rewrite (@fmap_id _ _ F x) in H.
  rewrite comp_id_r in H.
  rewrite <- comp_assoc in H.
  setoid_rewrite (comp_id_r (to i (x, F x) (id (F x)))) in H.
  etransitivity.
  2: exact H.
  clear H.
  generalize (naturality (to i) ((f, id (F y)): (_, _) ~> (_, _))).
  intros H.
  specialize (f_equal (fun f => f (id (F y))) H).
  clear H; intros H.
  simpl in H.
  unfold comp at 1 12 in H; simpl in H.
  unfold Typ.comp in H.
  rewrite comp_id_r in H.
  rewrite fmap_id, !comp_id_l in H.
  symmetry.
  exact H.
Qed.

Program Definition hom_counit: F ∘ G ~> id D := {|
  transform x := (to i⁻¹ (G x, x) (id (G x)));
|}.
Next Obligation.
  generalize (naturality (from i) ((id (G x: co C), f): (_, x) ~> (_, y))).
  intros H.
  specialize (f_equal (fun f => f (id (G x))) H).
  clear H; intros H.
  simpl in H.
  unfold comp at 1 12 in H; simpl in H.
  unfold Typ.comp in H.
  rewrite comp_id_r in H.
  setoid_rewrite (comp_id_r (fmap G f)) in H.
  setoid_rewrite (@fmap_id _ _ F (G x)) in H.
  rewrite comp_id_r in H.
  rewrite <- H; clear H.
  generalize (naturality (from i) ((fmap G f, id y): (_, _) ~> (_, _))).
  intros H.
  specialize (f_equal (fun f => f (id (G y))) H).
  clear H; intros H.
  simpl in H.
  unfold comp at 1 12 in H; simpl in H.
  unfold Typ.comp in H.
  rewrite comp_id_r, comp_id_l in H.
  rewrite fmap_id, comp_id_l in H.
  symmetry.
  apply H.
Qed.

Lemma hom_unit_naturality {x y} (f: F x ~> y): to i (x, y) f = fmap G f ∘ hom_unit x.
Proof.
  generalize (naturality (to i) ((id (x: co C), f): (_, _) ~> (_, _))).
  intros H.
  generalize (f_equal (fun f => f (id (F x))) H).
  clear H; intros H.
  simpl in H.
  unfold comp at 1 12 in H; simpl in H.
  unfold Typ.comp in H.
  setoid_rewrite (@fmap_id _ _ F x) in H.
  rewrite !comp_id_r in H.
  rewrite <- comp_assoc in H.
  setoid_rewrite (comp_id_r (to i (x, F x) (id (F x)))) in H.
  exact H.
Qed.

Lemma hom_counit_naturality {x y} (f: x ~> G y): to i⁻¹ (x, y) f = hom_counit y ∘ fmap F f.
Proof.
  generalize (naturality (from i) ((f, id y): (_, _) ~> (_, _))).
  intros H.
  generalize (f_equal (fun f => f (id (G y))) H).
  clear H; intros H.
  simpl in H.
  unfold comp at 1 12 in H; simpl in H.
  unfold Typ.comp in H.
  rewrite fmap_id, !comp_id_l in H.
  exact H.
Qed.

Lemma hom_adjoint_by: adjoint_by F G hom_counit hom_unit.
Proof.
  apply adjoint_by_alt.
  split; intros x.
  all: etransitivity.
  1, 3: symmetry.
  exact (hom_counit_naturality (hom_unit x)).
  exact (hom_unit_naturality (hom_counit x)).
  all: simpl.
  1: change ((i⁻¹ ∘ i) (x, F x) (id (F x)) = id (F x)).
  2: change ((i ∘ i⁻¹) (G x, x) (id (G x)) = id (G x)).
  1: rewrite inv_l.
  2: rewrite inv_r.
  all: reflexivity.
Qed.

End Hom2Adjoint.

Lemma adjoint_hom {C D: Category} (F: C ~> D) (G: D ~> C): F -| G <-> Hom D ∘ ⟨cof F ∘ π₁, π₂⟩ ≃ Hom C ∘ ⟨π₁, G ∘ π₂⟩.
Proof.
  split.
  + intros [ɛ [η adj]].
    constructor.
    exact (adjoint_hom_iso F G ɛ η adj).
  + intros [i].
    exists (hom_counit F G i), (hom_unit F G i).
    exact (hom_adjoint_by F G i).
Qed.
