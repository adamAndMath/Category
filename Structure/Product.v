Require Export Base.

Module ProdCategory.

Structure mixin_of (C: Category) := Mixin {
  prod: C -> C -> C;
  fork {a b c: C}: a ~> b -> a ~> c -> a ~> prod b c;
  pi1 {a b: C}: prod a b ~> a;
  pi2 {a b: C}: prod a b ~> b;
  fork_pi {a b c: C} (f: a ~> b) (g: a ~> c) (h: a ~> prod b c): h = fork f g <-> pi1 ∘ h = f /\ pi2 ∘ h = g;
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
Notation ProdCategory := type.
  
End Exports.

End ProdCategory.

Export ProdCategory.Exports.

Section Product.
Context {C: ProdCategory}.

Definition prod: C -> C -> C := ProdCategory.prod C (ProdCategory.class C).
Definition fork: forall {a b c: C}, a ~> b -> a ~> c -> a ~> prod b c := @ProdCategory.fork C (ProdCategory.class C).
Definition pi1: forall {a b: C}, prod a b ~> a := @ProdCategory.pi1 C (ProdCategory.class C).
Definition pi2: forall {a b: C}, prod a b ~> b := @ProdCategory.pi2 C (ProdCategory.class C).

Infix "×" := prod (at level 40, left associativity).
Notation "⟨ f , g ⟩" := (fork f g).
Notation π₁ := pi1.
Notation π₂ := pi2.

Lemma fork_pi {a b c: C} (f: a ~> b) (g: a ~> c) (h: a ~> b × c): h = ⟨f, g⟩ <-> π₁ ∘ h = f /\ π₂ ∘ h = g.
Proof. apply ProdCategory.fork_pi. Qed.

Lemma pi1_fork {a b c: C} (f: a ~> b) (g: a ~> c): π₁ ∘ ⟨f, g⟩ = f.
Proof. now apply fork_pi with g. Qed.

Lemma pi2_fork {a b c: C} (f: a ~> b) (g: a ~> c): π₂ ∘ ⟨f, g⟩ = g.
Proof. now apply fork_pi with f. Qed.

Lemma fork_eta {a b c: C} (f: a ~> b × c): ⟨π₁ ∘ f, π₂ ∘ f⟩ = f.
Proof.
  symmetry.
  now apply fork_pi.
Qed.

Lemma fork_inj {a b c: C} (f f': a ~> b) (g g': a ~> c):
  ⟨f, g⟩ = ⟨f', g'⟩ <-> f = f' /\ g = g'.
Proof.
  symmetry.
  split.
  all: intros H.
  now f_equiv.
  split.
  1: rewrite <- (pi1_fork f g).
  2: rewrite <- (pi2_fork f g).
  all: rewrite H.
  apply pi1_fork.
  apply pi2_fork.
Qed.

Lemma fork_comp {a b c d: C} (f: b ~> c) (g: b ~> d) (h: a ~> b): ⟨f, g⟩ ∘ h = ⟨f ∘ h, g ∘ h⟩.
Proof.
  apply fork_pi.
  split.
  all: rewrite comp_assoc.
  all: f_equal.
  apply pi1_fork.
  apply pi2_fork.
Qed.

Definition fprod {a b c d: C} (f: a ~> b) (g: c ~> d): a × c ~> b × d :=
  ⟨ f ∘ π₁, g ∘ π₂⟩.

Infix "(×)" := fprod (at level 40, left associativity).

Lemma fprod_id (a b: C): id a (×) id b = id (a × b).
Proof.
  symmetry.
  apply fork_pi.
  now rewrite !comp_id_l, !comp_id_r.
Qed.

Lemma fprod_comp {a a' b b' c c': C} (f: b ~> c) (f': b' ~> c') (g: a ~> b) (g': a' ~> b'): (f (×) f') ∘ (g (×) g') = (f ∘ g) (×) (f' ∘ g').
Proof.
  unfold fprod.
  rewrite fork_comp.
  f_equal.
  all: rewrite <- !comp_assoc.
  all: f_equal.
  apply pi1_fork.
  apply pi2_fork.
Qed.

Lemma fprod_inv_l {a b c d: C} (f: a <~> b) (g: c <~> d): (f⁻¹ (×) g⁻¹) ∘ (f (×) g) = id (a × c).
Proof.
  rewrite fprod_comp, <- fprod_id.
  f_equal.
  all: apply inv_l.
Qed.

Lemma fprod_inv_r {a b c d: C} (f: a <~> b) (g: c <~> d): (f (×) g) ∘ (f⁻¹ (×) g⁻¹) = id (b × d).
Proof.
  rewrite fprod_comp, <- fprod_id.
  f_equal.
  all: apply inv_r.
Qed.

Definition iprod {a b c d: C} (f: a <~> b) (g: c <~> d): a × c <~> b × d :=
  Isomorphism.Pack (f (×) g) (Isomorphism.Mixin _ _ _ (f (×) g) (f⁻¹ (×) g⁻¹) (fprod_inv_l f g) (fprod_inv_r f g)).

Lemma is_iso_fprod {a b c d: C} (f: a ~> b) (g: c ~> d): is_iso f -> is_iso g -> is_iso (f (×) g).
Proof.
  intros [f' [Hfl Hfr]] [g' [Hgl Hgr]].
  exists (f' (×) g'); split.
  all: rewrite fprod_comp, <- fprod_id.
  all: now f_equal.
Qed.

Global Instance prod_iso: Proper (isomorphic C ==> isomorphic C ==> isomorphic C) prod.
Proof.
  intros x x' [f] y y' [g].
  constructor.
  exact (iprod f g).
Qed.

End Product.

Infix "×" := prod (at level 40, left associativity).
Infix "(×)" := fprod (at level 40, left associativity).
Notation "⟨ f , g ⟩" := (fork f g).
Canonical iprod.
Notation π₁ := pi1.
Notation π₂ := pi2.
