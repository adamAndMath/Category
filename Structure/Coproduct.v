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

Lemma merge_comp {a b c d: C} (f: c ~> d) (g: a ~> c) (h: b ~> c): f ∘ [g, h] = [f ∘ g, f ∘ h].
Proof.
  apply merge_in.
  split.
  all: rewrite <- comp_assoc.
  all: f_equal.
  apply merge_in1.
  apply merge_in2.
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

Definition fcoprod {a b c d: C} (f: a ~> b) (g: c ~> d): a + c ~> b + d :=
  [in1 ∘ f, in2 ∘ g ].

Infix "(+)" := fcoprod (at level 50, left associativity).

Lemma fcoprod_id (a b: C): id a (+) id b = id (a + b).
Proof.
  symmetry.
  apply merge_in.
  now rewrite !comp_id_l, !comp_id_r.
Qed.

Lemma fcoprod_comp {a a' b b' c c': C} (f: b ~> c) (f': b' ~> c') (g: a ~> b) (g': a' ~> b'): (f (+) f') ∘ (g (+) g') = (f ∘ g) (+) (f' ∘ g').
Proof.
  unfold fcoprod.
  rewrite merge_comp.
  f_equal.
  all: rewrite !comp_assoc.
  all: f_equal.
  apply merge_in1.
  apply merge_in2.
Qed.

Lemma fcoprod_inv_l {a b c d: C} (f: a <~> b) (g: c <~> d): (f⁻¹ (+) g⁻¹) ∘ (f (+) g) = id (a + c).
Proof.
  rewrite fcoprod_comp, <- fcoprod_id.
  f_equal.
  all: apply inv_l.
Qed.

Lemma fcoprod_inv_r {a b c d: C} (f: a <~> b) (g: c <~> d): (f (+) g) ∘ (f⁻¹ (+) g⁻¹) = id (b + d).
Proof.
  rewrite fcoprod_comp, <- fcoprod_id.
  f_equal.
  all: apply inv_r.
Qed.

Definition icoprod {a b c d: C} (f: a <~> b) (g: c <~> d): a + c <~> b + d :=
  Isomorphism.Pack (f (+) g) (Isomorphism.Mixin _ _ _ (f (+) g) (f⁻¹ (+) g⁻¹) (fcoprod_inv_l f g) (fcoprod_inv_r f g)).

Lemma is_iso_fcoprod {a b c d: C} (f: a ~> b) (g: c ~> d): is_iso f -> is_iso g -> is_iso (f (+) g).
Proof.
  intros [f' [Hfl Hfr]] [g' [Hgl Hgr]].
  exists (f' (+) g'); split.
  all: rewrite fcoprod_comp, <- fcoprod_id.
  all: now f_equal.
Qed.

Global Instance coprod_iso: Proper (isomorphic C ==> isomorphic C ==> isomorphic C) coprod.
Proof.
  intros x x' [f] y y' [g].
  constructor.
  exact (icoprod f g).
Qed.

End Coproduct.

Infix "+" := coprod (at level 50, left associativity).
Infix "(+)" := fcoprod (at level 50, left associativity).
Notation "[ f , g ]" := (merge f g).
Canonical icoprod.
