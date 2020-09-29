Require Export Base.

Module EqCategory.

Structure mixin_of (C: Category) := Mixin {
  Eqz {x y: C} (f g: x ~> y): C;
  eqz {x y: C} (f g: x ~> y): Eqz f g ~> x;
  eqz_comm {x y: C} (f g: x ~> y): f ∘ eqz f g = g ∘ eqz f g;
  eqz_uni {x y z: C} (f g: y ~> z) (e: x ~> y): f ∘ e = g ∘ e -> {u: x ~> Eqz f g | eqz f g ∘ u = e}
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
Notation EqCategory := type.

End Exports.

End EqCategory.

Export EqCategory.Exports.

Section Equalizer.
Context {C: EqCategory}.

Definition Eqz: forall {x y: C} (f g: x ~> y), C := @EqCategory.Eqz C (EqCategory.class C).
Definition eqz: forall {x y: C} (f g: x ~> y), Eqz f g ~> x := @EqCategory.eqz C (EqCategory.class C).
Definition eqz_uni: forall {x y z: C} (f g: y ~> z) (e: x ~> y), f ∘ e = g ∘ e -> {u: x ~> Eqz f g | eqz f g ∘ u = e} := @EqCategory.eqz_uni C (EqCategory.class C).

Lemma eqz_comm: forall {x y: C} (f g: x ~> y), f ∘ eqz f g = g ∘ eqz f g.
Proof. apply EqCategory.eqz_comm. Qed.

End Equalizer.
