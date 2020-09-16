Require Export Structure.

Definition Poset_mixin {T} (R: T -> T -> Prop) {pre: PreOrder R} {po: PartialOrder eq R}: Category.mixin_of T :=
  Category.Mixin T R reflexivity (fun _ _ _ f g => transitivity g f)
  (fun _ _ _ _ _ _ _ => proof_irrelevance _ _ _)
  (fun _ _ _ => proof_irrelevance _ _ _)
  (fun _ _ _ => proof_irrelevance _ _ _).

Definition Poset {T: Type} (R: T -> T -> Prop) {pre: PreOrder R} {po: PartialOrder eq R}: Category :=
  Category.Pack T (Poset_mixin R).

Lemma Poset_hom_eq {T: Type} {R: T -> T -> Prop} {pre: PreOrder R} {po: PartialOrder eq R} {x y: Poset R} (f g: x ~> y): f = g.
Proof.
  simpl in *.
  unfold hom in f, g.
  simpl in *.
  assert (f = g).
  apply proof_irrelevance.
  exact H.
Qed.
