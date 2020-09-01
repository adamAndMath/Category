Require Export Category.

Module ProdCategory.

Structure mixin_of (C: Category) := Mixin {
  prod: C -> C -> C;
  join {a b c: C}: a ~> b -> a ~> c -> a ~> prod b c;
  pi1 {a b: C}: prod a b ~> a;
  pi2 {a b: C}: prod a b ~> b;
  pi1_join {a b c: C} (f: a ~> b) (g: a ~> c): pi1 ∘ join f g = f;
  pi2_join {a b c: C} (f: a ~> b) (g: a ~> c): pi2 ∘ join f g = g;
  join_pi {a b c: C} (f: a ~> prod b c): join (pi1 ∘ f) (pi2 ∘ f) = f;
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
Notation ProdCategory := type.
  
End Exports.

End ProdCategory.

Export ProdCategory.Exports.

Section Product.
Context {C: ProdCategory}.

Definition prod: C -> C -> C := ProdCategory.prod C (ProdCategory.class C).
Definition join: forall {a b c: C}, a ~> b -> a ~> c -> a ~> prod b c := @ProdCategory.join C (ProdCategory.class C).
Definition pi1: forall {a b: C}, prod a b ~> a := @ProdCategory.pi1 C (ProdCategory.class C).
Definition pi2: forall {a b: C}, prod a b ~> b := @ProdCategory.pi2 C (ProdCategory.class C).

Infix "×" := prod (at level 40, left associativity).
Notation "⟨ f , g ⟩" := (join f g).
Notation π₁ := pi1.
Notation π₂ := pi2.

Lemma pi1_join {a b c: C} (f: a ~> b) (g: a ~> c): pi1 ∘ join f g = f.
Proof. apply ProdCategory.pi1_join. Qed.
Lemma pi2_join {a b c: C} (f: a ~> b) (g: a ~> c): pi2 ∘ join f g = g.
Proof. apply ProdCategory.pi2_join. Qed.
Lemma join_pi {a b c: C} (f: a ~> prod b c): join (pi1 ∘ f) (pi2 ∘ f) = f.
Proof. apply ProdCategory.join_pi. Qed.

Lemma join_inj {a b c: C} (f f': a ~> b) (g g': a ~> c):
  ⟨f, g⟩ = ⟨f', g'⟩ <-> f = f' /\ g = g'.
Proof.
  symmetry.
  split.
  all: intros H.
  now f_equiv.
  split.
  1: rewrite <- (pi1_join f g).
  2: rewrite <- (pi2_join f g).
  all: rewrite H.
  apply pi1_join.
  apply pi2_join.
Qed.

End Product.

Infix "×" := prod (at level 40, left associativity).
Notation "⟨ f , g ⟩" := (join f g).
Notation π₁ := pi1.
Notation π₂ := pi2.

