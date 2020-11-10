Require Export Structure.

Definition fixpoint {C: Category} (F: C ~> C) (X: C) :=
  F X ≃ X.

Module Algebra.

Section category.
Context {C: Category} (F: C ~> C).

Structure obj := Obj {
  carrier: C;
  law: F carrier ~> carrier;
}.

Lemma obj_eq (A B: obj): A = B <-> carrier A = carrier B /\ forall e: carrier A = carrier B, eq_iso e ∘ law A = law B ∘ fmap F (eq_iso e).
Proof.
  split.
  intros H.
  subst B.
  repeat split.
  intros e.
  rewrite eq_iso_refl; clear e.
  simpl.
  rewrite fmap_id, comp_id_r.
  apply comp_id_l.
  destruct A as [A f], B as [B g].
  simpl.
  intros [AB H].
  subst B.
  f_equal.
  specialize (H eq_refl).
  simpl in H.
  rewrite fmap_id, comp_id_l, comp_id_r in H.
  exact H.
Qed.

Structure hom (A B: obj) := Hom {
  arr: carrier A ~> carrier B;
  comm: law B ∘ fmap F arr = arr ∘ law A;
}.

Lemma hom_eq {A B: obj} (f g: hom A B): f = g <-> arr _ _ f = arr _ _ g.
Proof.
  split.
  intros H.
  now subst g.
  destruct f as [f Hf], g as [g Hg].
  simpl.
  intros H.
  subst g.
  f_equal.
  apply proof_irrelevance.
Qed.

Program Definition id A: hom A A := {|
  arr := id (carrier A);
|}.
Next Obligation.
  rewrite fmap_id, comp_id_l.
  apply comp_id_r.
Qed.

Program Definition comp {A B C} (f: hom B C) (g: hom A B): hom A C := {|
  arr := arr _ _ f ∘ arr _ _ g;
|}.
Next Obligation.
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite comm.
  rewrite <- !comp_assoc.
  f_equal.
  apply comm.
Qed.

Lemma comp_assoc {a b c d} (f: hom c d) (g: hom b c) (h: hom a b): comp f (comp g h) = comp (comp f g) h.
Proof.
  apply hom_eq; simpl.
  apply comp_assoc.
Qed.

Lemma comp_id_l {A B} (f: hom A B): comp (id B) f = f.
Proof.
  apply hom_eq; simpl.
  apply comp_id_l.
Qed.

Lemma comp_id_r {A B} (f: hom A B): comp f (id A) = f.
Proof.
  apply hom_eq; simpl.
  apply comp_id_r.
Qed.

Definition cat_mixin: Category.mixin_of obj :=
  Category.Mixin obj hom id (@comp) (@comp_assoc) (@comp_id_l) (@comp_id_r).

Definition cat: Category :=
  Category.Pack obj cat_mixin.

End category.

Arguments Obj {C F} carrier law.
Arguments carrier {C F} _.
Arguments law {C F} _.
Arguments hom {C F} A B.
Arguments Hom {C F A B} arr comm.
Arguments arr {C F A B} _.
Arguments comm {C F A B} _.

End Algebra.

Coercion Algebra.carrier: Algebra.obj >-> Category.obj.
Coercion Algebra.arr: Algebra.hom >-> Categories.hom.
Canonical Algebra.cat.
Notation Algebra := Algebra.cat.

Module Coalgebra.

Section category.
Context {C: Category} (F: C ~> C).

Structure obj := Obj {
  carrier: C;
  law: carrier ~> F carrier;
}.

Lemma obj_eq (A B: obj): A = B <-> carrier A = carrier B /\ forall e: carrier A = carrier B, fmap F (eq_iso e) ∘ law A = law B ∘ eq_iso e.
Proof.
  split.
  intros H.
  subst B.
  repeat split.
  intros e.
  rewrite eq_iso_refl; clear e.
  simpl.
  rewrite fmap_id, comp_id_r.
  apply comp_id_l.
  destruct A as [A f], B as [B g].
  simpl.
  intros [AB H].
  subst B.
  f_equal.
  specialize (H eq_refl).
  simpl in H.
  rewrite fmap_id, comp_id_l, comp_id_r in H.
  exact H.
Qed.

Structure hom (A B: obj) := Hom {
  arr: carrier A ~> carrier B;
  comm: fmap F arr ∘ law A = law B ∘ arr;
}.

Lemma hom_eq {A B: obj} (f g: hom A B): f = g <-> arr _ _ f = arr _ _ g.
Proof.
  split.
  intros H.
  now subst g.
  destruct f as [f Hf], g as [g Hg].
  simpl.
  intros H.
  subst g.
  f_equal.
  apply proof_irrelevance.
Qed.

Program Definition id A: hom A A := {|
  arr := id (carrier A);
|}.
Next Obligation.
  rewrite fmap_id, comp_id_r.
  apply comp_id_l.
Qed.

Program Definition comp {A B C} (f: hom B C) (g: hom A B): hom A C := {|
  arr := arr _ _ f ∘ arr _ _ g;
|}.
Next Obligation.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite comm.
  rewrite !comp_assoc.
  f_equal.
  apply comm.
Qed.

Lemma comp_assoc {a b c d} (f: hom c d) (g: hom b c) (h: hom a b): comp f (comp g h) = comp (comp f g) h.
Proof.
  apply hom_eq; simpl.
  apply comp_assoc.
Qed.

Lemma comp_id_l {A B} (f: hom A B): comp (id B) f = f.
Proof.
  apply hom_eq; simpl.
  apply comp_id_l.
Qed.

Lemma comp_id_r {A B} (f: hom A B): comp f (id A) = f.
Proof.
  apply hom_eq; simpl.
  apply comp_id_r.
Qed.

Definition cat_mixin: Category.mixin_of obj :=
  Category.Mixin obj hom id (@comp) (@comp_assoc) (@comp_id_l) (@comp_id_r).

Definition cat: Category :=
  Category.Pack obj cat_mixin.

End category.

Arguments Obj {C F} carrier law.
Arguments carrier {C F} _.
Arguments law {C F} _.
Arguments hom {C F} A B.
Arguments Hom {C F A B} arr comm.
Arguments arr {C F A B} _.
Arguments comm {C F A B} _.

End Coalgebra.

Coercion Coalgebra.carrier: Coalgebra.obj >-> Category.obj.
Coercion Coalgebra.arr: Coalgebra.hom >-> Categories.hom.
Canonical Coalgebra.cat.
Notation Coalgebra := Coalgebra.cat.

Section algebra_cof.
Context {C: Category} (F: C ~> C).

Program Definition algebra_cof_to: co (Algebra F) ~> Coalgebra (cof F) := {|
  fobj A := {|
    Coalgebra.carrier := A;
    Coalgebra.law := Algebra.law A;
  |};
  fmap A B f := {|
    Coalgebra.arr := f;
    Coalgebra.comm := Algebra.comm f;
  |};
|}.
Next Obligation.
  now apply Coalgebra.hom_eq.
Qed.
Next Obligation.
  now apply Coalgebra.hom_eq.
Qed.

Program Definition algebra_cof_from: Coalgebra (cof F) ~> co (Algebra F) := {|
  fobj A := {|
    Algebra.carrier := A;
    Algebra.law := Coalgebra.law A;
  |};
  fmap A B f := {|
    Algebra.arr := f;
    Algebra.comm := Coalgebra.comm f;
  |};
|}.
Next Obligation.
  now apply Algebra.hom_eq.
Qed.
Next Obligation.
  now apply Algebra.hom_eq.
Qed.

Lemma algebra_cof_inv_l: algebra_cof_from ∘ algebra_cof_to = id (co (Algebra F)).
Proof.
  fun_eq x y f.
  now destruct x.
  destruct x as [X x], y as [Y y], f as [f Hf].
  simpl in *.
  rewrite !eq_iso_refl; clear H H0.
  simpl.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Lemma algebra_cof_inv_r: algebra_cof_to ∘ algebra_cof_from = id (Coalgebra (cof F)).
Proof.
  fun_eq x y f.
  now destruct x.
  destruct x as [X x], y as [Y y], f as [f Hf].
  simpl in *.
  rewrite !eq_iso_refl; clear H H0.
  simpl.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Canonical algebra_cof: co (Algebra F) <~> Coalgebra (cof F) :=
  Isomorphism.Pack algebra_cof_to (Isomorphism.Mixin _ _ _ algebra_cof_to algebra_cof_from algebra_cof_inv_l algebra_cof_inv_r).

Lemma algebra_co: co (Algebra F) ≃ Coalgebra (cof F).
Proof.
  constructor.
  exact algebra_cof.
Qed.

End algebra_cof.

Section coalgebra_cof.
Context {C: Category} (F: C ~> C).

Program Definition coalgebra_cof_to: co (Coalgebra F) ~> Algebra (cof F) := {|
  fobj A := {|
    Algebra.carrier := A;
    Algebra.law := Coalgebra.law A;
  |};
  fmap A B f := {|
    Algebra.arr := f;
    Algebra.comm := Coalgebra.comm f;
  |};
|}.
Next Obligation.
  now apply Algebra.hom_eq.
Qed.
Next Obligation.
  now apply Algebra.hom_eq.
Qed.

Program Definition coalgebra_cof_from: Algebra (cof F) ~> co (Coalgebra F) := {|
  fobj A := {|
    Coalgebra.carrier := A;
    Coalgebra.law := Algebra.law A;
  |};
  fmap A B f := {|
    Coalgebra.arr := f;
    Coalgebra.comm := Algebra.comm f;
  |};
|}.
Next Obligation.
  now apply Coalgebra.hom_eq.
Qed.
Next Obligation.
  now apply Coalgebra.hom_eq.
Qed.

Lemma coalgebra_cof_inv_l: coalgebra_cof_from ∘ coalgebra_cof_to = id (co (Coalgebra F)).
Proof.
  fun_eq x y f.
  now destruct x.
  destruct x as [X x], y as [Y y], f as [f Hf].
  simpl in *.
  rewrite !eq_iso_refl; clear H H0.
  simpl.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Lemma coalgebra_cof_inv_r: coalgebra_cof_to ∘ coalgebra_cof_from = id (Algebra (cof F)).
Proof.
  fun_eq x y f.
  now destruct x.
  destruct x as [X x], y as [Y y], f as [f Hf].
  simpl in *.
  rewrite !eq_iso_refl; clear H H0.
  simpl.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Canonical coalgebra_cof: co (Coalgebra F) <~> Algebra (cof F) :=
  Isomorphism.Pack coalgebra_cof_to (Isomorphism.Mixin _ _ _ coalgebra_cof_to coalgebra_cof_from coalgebra_cof_inv_l coalgebra_cof_inv_r).

Lemma coalgebra_co: co (Coalgebra F) ≃ Algebra (cof F).
Proof.
  constructor.
  exact coalgebra_cof.
Qed.

End coalgebra_cof.

(* is_initial coincieds with initial objects *)
Definition is_final {C: Category} {F: C ~> C} (A: Coalgebra F) := is_terminal A.

Lemma is_final_co {C: Category} {F: C ~> C} (A: Algebra F): is_initial A <-> is_final (to (algebra_cof F) A).
Proof.
  split.
  + intros H B'.
    assert (exists B, to (algebra_cof F) B = B').
      exists (to (algebra_cof F)⁻¹ B').
      change ((algebra_cof F ∘ (algebra_cof F)⁻¹) B' = B').
      now rewrite inv_r.
    destruct H0 as [B].
    subst B'.
    specialize (H B).
    destruct H as [f H].
    exists (fmap (to (algebra_cof F)) f).
    intros g'.
    destruct (iso_full _ _ _ g') as [g Hg].
    subst g'.
    now f_equal.
  + intros H B.
    specialize (H (to (algebra_cof F) B)).
    destruct H as [f' H].
    destruct (iso_full _ _ _ f') as [f Hf].
    subst f'.
    exists f.
    intros g.
    now apply (iso_faithful (algebra_cof F)).
Qed.
