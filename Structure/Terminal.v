Require Export Category.

Module TopCategory.

Structure mixin_of (C: Category) := Mixin {
  one: C;
  to_one {a: C}: a ~> one;
  to_one_comp (a b: C) (f: a ~> b): to_one ∘ f = to_one;
  one_to_one: @to_one one = id one;
}.

Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type := Pack { sort: Category; _: class_of sort }.
Local Coercion sort: type >-> Category.

Variable T: type.
Definition class := match T return class_of T with Pack _ c => c end.

End ClassDef.

Module Exports.

Coercion sort: type >-> Category.
Notation TopCategory := type.

End Exports.

End TopCategory.

Export TopCategory.Exports.

Section Terminal.
Context {C: TopCategory}.

Definition one: C := TopCategory.one C (TopCategory.class C).
Definition to_one: forall {a: C}, a ~> one := @TopCategory.to_one C (TopCategory.class C).

Lemma to_one_comp {a b: C} (f: a ~> b): to_one ∘ f = to_one.
Proof. apply TopCategory.to_one_comp. Qed.

Lemma one_to_one: @to_one one = id one.
Proof. apply TopCategory.one_to_one. Qed.

Lemma to_one_unique {a: C} (f: a ~> one): f = to_one.
Proof.
  rewrite <- (comp_id_l f).
  rewrite <- (to_one_comp f).
  f_equiv.
  symmetry.
  apply one_to_one.
Qed.

End Terminal.

Notation "1" := one.

