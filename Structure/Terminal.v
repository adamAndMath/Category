Require Export Base.

Module TopCategory.

Structure mixin_of (C: Category) := Mixin {
  one: C;
  to_one {a: C}: a ~> one;
  to_one_unique {a: C} (f: a ~> one): @to_one a = f;
}.

Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type := Pack { sort: Category; _: class_of sort }.
Local Coercion sort: type >-> Category.

Variable T: type.
Definition class := match T return class_of T with Pack _ c => c end.

Definition Cat: Cat := T.

End ClassDef.

Module Exports.

Coercion sort: type >-> Category.
Coercion Cat: type >-> Category.obj.
Notation TopCategory := type.

End Exports.

End TopCategory.

Export TopCategory.Exports.

Section Terminal.
Context {C: TopCategory}.

Definition one: C := TopCategory.one C (TopCategory.class C).
Definition to_one: forall {a: C}, a ~> one := @TopCategory.to_one C (TopCategory.class C).

Lemma to_one_unique {a: C} (f: a ~> one): to_one = f.
Proof. apply TopCategory.to_one_unique. Qed.

Lemma to_one_comp {a b: C} (f: a ~> b): to_one ∘ f = to_one.
Proof.
  symmetry.
  apply to_one_unique.
Qed.

Lemma one_to_one: @to_one one = id one.
Proof. apply to_one_unique. Qed.

End Terminal.

Notation "1" := one.

