Require Export Base.

Module BotCategory.

Structure mixin_of (C: Category) := Mixin {
  zero: C;
  from_zero {a: C}: zero ~> a;
  from_zero_unique (a: C) (f: zero ~> a): from_zero = f;
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
Notation BotCategory := type.

End Exports.

End BotCategory.

Export BotCategory.Exports.

Section Initial.
Context {C: BotCategory}.

Definition zero: C := BotCategory.zero C (BotCategory.class C).
Definition from_zero: forall {a: C}, zero ~> a := @BotCategory.from_zero C (BotCategory.class C).

Lemma from_zero_unique {a: C} (f: zero ~> a): from_zero = f.
Proof. apply BotCategory.from_zero_unique. Qed.

Lemma from_zero_comp {a b: C} (f: a ~> b): f ∘ from_zero = from_zero.
Proof.
  symmetry.
  apply from_zero_unique.
Qed.

Lemma zero_to_zero: @from_zero zero = id zero.
Proof. apply from_zero_unique. Qed.

End Initial.

Notation "0" := zero.

