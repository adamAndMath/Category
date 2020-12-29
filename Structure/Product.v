Require Export Base.

Definition is_product {C: Category} (a b p: C) (p1: p ~> a) (p2: p ~> b) :=
  forall (z: C) (f: z ~> a) (g: z ~> b), exists! h: z ~> p, p1 ∘ h = f /\ p2 ∘ h = g.

Definition is_prod_obj {C: Category} (a b p: C) :=
  exists (p1: p ~> a) (p2: p ~> b), is_product a b p p1 p2.

Definition ex_product {C: Category} (a b: C) :=
  exists (p: C), is_prod_obj a b p.

Instance is_prod_obj_iso (C: Category): Proper (isomorphic C ==> isomorphic C ==> isomorphic C ==> iff) is_prod_obj.
Proof.
  enough (Proper (isomorphic C ==> isomorphic C ==> isomorphic C ==> impl) is_prod_obj).
  now split; apply H.
  intros a x [i] b y [j] p q [k] [p1 [p2 H]].
  exists (i ∘ p1 ∘ k⁻¹), (j ∘ p2 ∘ k⁻¹).
  intros z f' g'.
  assert (exists f: z ~> a, i ∘ f = f').
    exists (i⁻¹ ∘ f').
    rewrite comp_assoc, inv_r.
    apply comp_id_l.
  destruct H0 as [f].
  subst f'.
  assert (exists g: z ~> b, j ∘ g = g').
    exists (j⁻¹ ∘ g').
    rewrite comp_assoc, inv_r.
    apply comp_id_l.
  destruct H0 as [g].
  subst g'.
  specialize (H z f g).
  destruct H as [h [[H1 H2] Hh]].
  subst f g.
  exists (k ∘ h).
  repeat split.
  1, 2: rewrite !comp_assoc.
  1, 2: f_equal.
  1, 2: rewrite <- comp_assoc, inv_l.
  1, 2: apply comp_id_r.
  intros h' [H1 H2].
  rewrite <- !comp_assoc in H1.
  rewrite <- !comp_assoc in H2.
  apply iso_monic in H1.
  apply iso_monic in H2.
  apply (iso_monic k⁻¹).
  rewrite comp_assoc, inv_l, comp_id_l.
  now apply Hh.
Qed.

Instance ex_product_iso (C: Category): Proper (isomorphic C ==> isomorphic C ==> iff) ex_product.
Proof.
  intros a x H1 b y H2.
  unfold ex_product.
  f_equiv.
  intros p.
  now f_equiv.
Qed.

Lemma prod_obj_euniqueness {C: Category} (a b: C): euniqueness (is_prod_obj a b).
Proof.
  intros p q [p1 [p2 Hp]] [q1 [q2 Hq]].
  destruct (Hq p p1 p2) as [f [Hf _]].
  destruct (Hp q q1 q2) as [g [Hg _]].
  constructor.
  exists f, g.
  all: symmetry.
  + specialize (Hp p p1 p2).
    destruct Hp as [p' [Hp H]].
    transitivity p'.
    symmetry.
    all: apply H.
    all: split.
    1, 2: apply comp_id_r.
    all: rewrite comp_assoc.
    now rewrite (proj1 Hg).
    now rewrite (proj2 Hg).
  + specialize (Hq q q1 q2).
    destruct Hq as [q' [Hq H]].
    transitivity q'.
    symmetry.
    all: apply H.
    all: split.
    1, 2: apply comp_id_r.
    all: rewrite comp_assoc.
    now rewrite (proj1 Hf).
    now rewrite (proj2 Hf).
Qed.

Lemma ex_product_eunique {C: Category} (a b: C): ex_product a b <-> exists!! p, is_prod_obj a b p.
Proof.
  rewrite <- eunique_existence.
  split.
  + intros H.
    split.
    now apply is_prod_obj_iso.
    split.
    exact H.
    apply prod_obj_euniqueness.
  + intros [_ [H _]].
    exact H.
Qed.

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

Lemma fork_id {a b: C}: ⟨π₁, π₂⟩ = id (a × b).
Proof.
  symmetry.
  apply fork_pi.
  split.
  all: apply comp_id_r.
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

Lemma fprod_fork {a b b' c c'} (f: b ~> c) (f': b' ~> c') (g: a ~> b) (g': a ~> b'): (f (×) f') ∘ ⟨g, g'⟩ = ⟨f ∘ g, f' ∘ g'⟩.
Proof.
  unfold fprod.
  rewrite fork_comp.
  f_equal.
  all: rewrite <- !comp_assoc.
  all: f_equal.
  apply pi1_fork.
  apply pi2_fork.
Qed.

Lemma fprod_comp {a a' b b' c c': C} (f: b ~> c) (f': b' ~> c') (g: a ~> b) (g': a' ~> b'): (f ∘ g) (×) (f' ∘ g') = (f (×) f') ∘ (g (×) g').
Proof.
  symmetry.
  unfold fprod at 2 3.
  rewrite <- !comp_assoc.
  apply fprod_fork.
Qed.

Lemma fprod_inv_l {a b c d: C} (f: a <~> b) (g: c <~> d): (f⁻¹ (×) g⁻¹) ∘ (f (×) g) = id (a × c).
Proof.
  rewrite <- fprod_comp, <- fprod_id.
  f_equal.
  all: apply inv_l.
Qed.

Lemma fprod_inv_r {a b c d: C} (f: a <~> b) (g: c <~> d): (f (×) g) ∘ (f⁻¹ (×) g⁻¹) = id (b × d).
Proof.
  rewrite <- fprod_comp, <- fprod_id.
  f_equal.
  all: apply inv_r.
Qed.

Definition iprod {a b c d: C} (f: a <~> b) (g: c <~> d): a × c <~> b × d :=
  Isomorphism.Pack (f (×) g) (Isomorphism.Mixin _ _ _ (f (×) g) (f⁻¹ (×) g⁻¹) (fprod_inv_l f g) (fprod_inv_r f g)).

Lemma is_iso_fprod {a b c d: C} (f: a ~> b) (g: c ~> d): is_iso f -> is_iso g -> is_iso (f (×) g).
Proof.
  intros [f' [Hfl Hfr]] [g' [Hgl Hgr]].
  exists (f' (×) g'); split.
  all: rewrite <- fprod_comp, <- fprod_id.
  all: now f_equal.
Qed.

Global Instance prod_iso: Proper (isomorphic C ==> isomorphic C ==> isomorphic C) prod.
Proof.
  intros x x' [f] y y' [g].
  constructor.
  exact (iprod f g).
Qed.

Definition flip (x y: C): x × y ~> y × x := ⟨π₂, π₁⟩.

Lemma flip_invol (x y: C): flip y x ∘ flip x y = id (x × y).
Proof.
  unfold flip.
  rewrite fork_comp, <- fork_id.
  f_equal.
  apply pi2_fork.
  apply pi1_fork.
Qed.

Canonical flip_iso (x y: C): x × y <~> y × x :=
  Isomorphism.Pack (flip x y) (Isomorphism.Mixin C _ _ (flip x y) (flip y x) (flip_invol x y) (flip_invol y x)).

Lemma prod_comm (x y: C): x × y ≃ y × x.
Proof.
  constructor.
  exact (flip_iso x y).
Qed.

Section prod_associator.
Context (x y z: C).

Definition prod_associator_to: x × (y × z) ~> (x × y) × z :=
  ⟨⟨π₁, π₁ ∘ π₂⟩, π₂ ∘ π₂⟩.

Definition prod_associator_from: (x × y) × z ~> x × (y × z) :=
  ⟨π₁ ∘ π₁, ⟨π₂ ∘ π₁, π₂⟩⟩.

Lemma prod_associator_inv_l: prod_associator_from ∘ prod_associator_to = id (x × (y × z)).
Proof.
  unfold prod_associator_to, prod_associator_from.
  rewrite fork_comp, <- fork_id.
  f_equal.
  rewrite <- comp_assoc.
  rewrite pi1_fork.
  apply pi1_fork.
  rewrite <- comp_id_l, <- fork_id.
  rewrite !fork_comp.
  f_equal.
  rewrite <- comp_assoc.
  rewrite pi1_fork.
  apply pi2_fork.
  apply pi2_fork.
Qed.

Lemma prod_associator_inv_r: prod_associator_to ∘ prod_associator_from = id (x × y × z).
Proof.
  unfold prod_associator_to, prod_associator_from.
  rewrite fork_comp, <- fork_id.
  f_equal.
  rewrite <- comp_id_l, <- fork_id.
  rewrite !fork_comp.
  f_equal.
  apply pi1_fork.
  rewrite <- comp_assoc.
  rewrite pi2_fork.
  apply pi1_fork.
  rewrite <- comp_assoc.
  rewrite pi2_fork.
  apply pi2_fork.
Qed.

Definition prod_associator: x × (y × z) <~> (x × y) × z :=
  Isomorphism.Pack prod_associator_to (Isomorphism.Mixin _ _ _ prod_associator_to prod_associator_from prod_associator_inv_l prod_associator_inv_r).

Lemma prod_assoc: x × (y × z) ≃ (x × y) × z.
Proof.
  constructor.
  exact prod_associator.
Qed.

End prod_associator.

Lemma prod_assoc_fork {a x y z: C} (f: a ~> x) (g: a ~> y) (h: a ~> z): prod_associator x y z ∘ ⟨f, ⟨g, h⟩⟩ = ⟨⟨f, g⟩, h⟩.
Proof.
  simpl.
  unfold prod_associator_to.
  rewrite !fork_comp.
  repeat f_equal.
  apply pi1_fork.
  all: rewrite <- comp_assoc.
  all: rewrite pi2_fork.
  apply pi1_fork.
  apply pi2_fork.
Qed.

Lemma prod_assoc_inv_fork {a x y z: C} (f: a ~> x) (g: a ~> y) (h: a ~> z): (prod_associator x y z)⁻¹ ∘ ⟨⟨f, g⟩, h⟩ = ⟨f, ⟨g, h⟩⟩.
Proof.
  rewrite <- prod_assoc_fork.
  rewrite comp_assoc.
  rewrite inv_l.
  apply comp_id_l.
Qed.

Lemma pi_is_product (a b: C): is_product a b (a × b) π₁ π₂.
Proof.
  intros z f g.
  exists ⟨f, g⟩.
  repeat split.
  apply pi1_fork.
  apply pi2_fork.
  intros h H.
  symmetry.
  now apply fork_pi.
Qed.

Lemma prod_is_prod_obj (a b: C): is_prod_obj a b (a × b).
Proof.
  exists π₁, π₂.
  apply pi_is_product.
Qed.

Definition FProd: Bifunctor C C C := {|
  bobj a b := a × b;
  bmap a1 a2 b1 b2 f g := f (×) g;
  bmap_id := fprod_id;
  bmap_comp a b c a' b' c' f g f' g' := fprod_comp f f' g g';
|}.

End Product.

Infix "×" := prod (at level 40, left associativity).
Infix "(×)" := fprod (at level 40, left associativity).
Notation "⟨ f , g ⟩" := (fork f g).
Canonical iprod.
Notation π₁ := pi1.
Notation π₂ := pi2.

Lemma product_correct C: inhabited (ProdCategory.mixin_of C) <-> (forall a b: C, ex_product a b).
Proof.
  split.
  + intros [[p fork p1 p2 H]] a b.
    exists (p a b), (p1 a b), (p2 a b).
    intros z f g.
    exists (fork z a b f g); split.
    now apply H.
    intros h Hh.
    symmetry.
    now apply H.
  + intros H.
    generalize (fun a => proj1 (ex_forall _) (H a)).
    clear H; intros H.
    apply ex_forall in H.
    destruct H as [P H].
    generalize (fun a => proj1 (ex_forall _) (H a)).
    clear H; intros H.
    apply ex_forall in H.
    destruct H as [p1 H].
    generalize (fun a => proj1 (ex_forall _) (H a)).
    clear H; intros H.
    apply ex_forall in H.
    destruct H as [p2 H].
    generalize (fun a b z f => proj1 (ex_forall _) (H a b z f)).
    clear H; intros H.
    generalize (fun a b z => proj1 (ex_forall _) (H a b z)).
    clear H; intros H.
    generalize (fun a b => proj1 (ex_forall _) (H a b)).
    clear H; intros H.
    generalize (fun a => proj1 (ex_forall _) (H a)).
    clear H; intros H.
    apply ex_forall in H.
    destruct H as [fo H].
    constructor.
    exists P (fun a b c => fo b c a) p1 p2.
    intros a b c f g h.
    specialize (H b c a f g).
    destruct H as [H u].
    split.
    intros Hh.
    now subst h.
    intros Hh.
    symmetry.
    now apply u.
Qed.
