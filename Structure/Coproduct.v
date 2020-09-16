Require Export Base.

Module CoprodCategory.

Structure mixin_of (C: Category) := Mixin {
  coprod: C -> C -> C;
  merge {a b c: C}: a ~> c -> b ~> c -> coprod a b ~> c;
  in1 {a b: C}: a ~> coprod a b;
  in2 {a b: C}: b ~> coprod a b;
  merge_in {a b c: C} (f: a ~> c) (g: b ~> c) (h: coprod a b ~> c): h = merge f g <-> h ∘ in1 = f /\ h ∘ in2 = g;
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
Notation CoprodCategory := type.

End Exports.

End CoprodCategory.

Export CoprodCategory.Exports.

Section Coproduct.
Context {C: CoprodCategory}.

Definition coprod: C -> C -> C := CoprodCategory.coprod C (CoprodCategory.class C).
Definition merge: forall {a b c: C}, a ~> c -> b ~> c -> coprod a b ~> c := @CoprodCategory.merge C (CoprodCategory.class C).
Definition in1: forall {a b: C}, a ~> coprod a b := @CoprodCategory.in1 C (CoprodCategory.class C).
Definition in2: forall {a b: C}, b ~> coprod a b := @CoprodCategory.in2 C (CoprodCategory.class C).

Infix "+" := coprod (at level 50, left associativity).
Notation "[ f , g ]" := (merge f g).

Lemma merge_in {a b c: C} (f: a ~> c) (g: b ~> c) (h: a + b ~> c): h = [f, g] <-> h ∘ in1 = f /\ h ∘ in2 = g.
Proof. apply CoprodCategory.merge_in. Qed.

Lemma merge_in1 {a b c: C} (f: a ~> c) (g: b ~> c): [f, g] ∘ in1 = f.
Proof. now apply merge_in with g. Qed.

Lemma merge_in2 {a b c: C} (f: a ~> c) (g: b ~> c): [f, g] ∘ in2 = g.
Proof. now apply merge_in with f. Qed.

Lemma merge_eta {a b c: C} (f: a + b ~> c): [f ∘ in1, f ∘ in2] = f.
Proof.
  symmetry.
  now apply merge_in.
Qed.

Lemma merge_inj {a b c: C} (f f': a ~> c) (g g': b ~> c):
  [f, g] = [f', g'] <-> f = f' /\ g = g'.
Proof.
  symmetry.
  split.
  all: intros H.
  now f_equiv.
  split.
  1: rewrite <- (merge_in1 f g).
  2: rewrite <- (merge_in2 f g).
  all: rewrite H.
  apply merge_in1.
  apply merge_in2.
Qed.

End Coproduct.

Infix "+" := coprod (at level 50, left associativity).
Notation "[ f , g ]" := (merge f g).
