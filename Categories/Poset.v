Require Export Base.

Module Proset.

Section category.
Context {T} (R: T -> T -> Prop) {pre: PreOrder R}.

Definition cat_mixin: Category.mixin_of T :=
  Category.Mixin T R reflexivity (fun _ _ _ f g => transitivity g f)
  (fun _ _ _ _ _ _ _ => proof_irrelevance _ _ _)
  (fun _ _ _ => proof_irrelevance _ _ _)
  (fun _ _ _ => proof_irrelevance _ _ _).

Definition cat: Category :=
  Category.Pack T cat_mixin.

Lemma hom_eq {x y: cat} (f g: x ~> y): f = g.
Proof.
  simpl in *.
  unfold hom in f, g.
  simpl in *.
  assert (f = g).
  apply proof_irrelevance.
  exact H.
Qed.

End category.

End Proset.

Notation Proset := Proset.cat.

Definition Poset {T} (R: T -> T -> Prop) {pre: PreOrder R} {po: PartialOrder eq R} := Proset R.

Lemma dual_proset {T} (R: T -> T -> Prop) {pre: PreOrder R}: co (Proset R) = Proset (flip R).
Proof.
  unfold co, Proset; simpl.
  f_equal.
  apply cat_mixin_eq; simpl.
  repeat split.
  intros x e.
  apply proof_irrelevance.
  intros x y z f g e1 e2 e3.
  apply proof_irrelevance.
Qed.

Lemma dual_poset {T} (R: T -> T -> Prop) {pre: PreOrder R} {po: PartialOrder eq R}: co (Poset R) = @Poset _ (flip R) _ (PartialOrder_inverse po).
Proof. apply dual_proset. Qed.
