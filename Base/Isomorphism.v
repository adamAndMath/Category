Require Export Categories.

Section monoepi.
Context {C: Category}.

Definition monic {a b: C} (f: a ~> b) :=
  forall c (g1 g2: c ~> a), f ∘ g1 = f ∘ g2 -> g1 = g2.

Definition epic {a b: C} (f: a ~> b) :=
  forall c (g1 g2: b ~> c), g1 ∘ f = g2 ∘ f -> g1 = g2.

Definition splitmonic {a b: C} (f: a ~> b) :=
  exists f': b ~> a, f' ∘ f = id a.

Definition splitepic {a b: C} (f: a ~> b) :=
  exists f': b ~> a, f ∘ f' = id b.

Lemma splitmonic_is_monic {a b: C} (f: a ~> b): splitmonic f -> monic f.
Proof.
  intros [f' Hf] c g1 g2 H.
  setoid_rewrite <- comp_id_l.
  rewrite <- Hf.
  rewrite <- !comp_assoc.
  now f_equal.
Qed.

Lemma splitepic_is_epic {a b: C} (f: a ~> b): splitepic f -> epic f.
Proof.
  intros [f' Hf] c g1 g2 H.
  setoid_rewrite <- comp_id_r.
  rewrite <- Hf.
  rewrite !comp_assoc.
  now f_equal.
Qed.

Lemma monic_id (a: C): monic (id a).
Proof.
  intros x f g H.
  now setoid_rewrite <- comp_id_l.
Qed.

Lemma epic_id (a: C): epic (id a).
Proof.
  intros x f g H.
  now setoid_rewrite <- comp_id_r.
Qed.

Lemma splitmonic_id (a: C): splitmonic (id a).
Proof.
  exists (id a).
  apply comp_id_l.
Qed.

Lemma splitepic_id (a: C): splitepic (id a).
Proof.
  exists (id a).
  apply comp_id_l.
Qed.

Lemma monic_comp {a b c: C} (f: b ~> c) (g: a ~> b): monic f -> monic g -> monic (f ∘ g).
Proof.
  intros Hf Hg x h1 h2 H.
  apply Hg, Hf.
  now rewrite !comp_assoc.
Qed.

Lemma epic_comp {a b c: C} (f: b ~> c) (g: a ~> b): epic f -> epic g -> epic (f ∘ g).
Proof.
  intros Hf Hg x h1 h2 H.
  apply Hf, Hg.
  now rewrite <- !comp_assoc.
Qed.

Lemma splitmonic_comp {a b c: C} (f: b ~> c) (g: a ~> b): splitmonic f -> splitmonic g -> splitmonic (f ∘ g).
Proof.
  intros [f' Hf] [g' Hg].
  exists (g' ∘ f').
  rewrite comp_assoc, <- (comp_assoc g').
  rewrite Hf, comp_id_r.
  apply Hg.
Qed.

Lemma splitepic_comp {a b c: C} (f: b ~> c) (g: a ~> b): splitepic f -> splitepic g -> splitepic (f ∘ g).
Proof.
  intros [f' Hf] [g' Hg].
  exists (g' ∘ f').
  rewrite comp_assoc, <- (comp_assoc f).
  rewrite Hg, comp_id_r.
  apply Hf.
Qed.

Lemma monic_comp_r {a b c: C} (f: b ~> c) (g: a ~> b): monic (f ∘ g) -> monic g.
Proof.
  intros Hc x h1 h2 H.
  apply Hc.
  rewrite <- !comp_assoc.
  now f_equal.
Qed.

Lemma epic_comp_l {a b c: C} (f: b ~> c) (g: a ~> b): epic (f ∘ g) -> epic f.
Proof.
  intros Hc x h1 h2 H.
  apply Hc.
  rewrite !comp_assoc.
  now f_equal.
Qed.

Lemma splitmonic_comp_r {a b c: C} (f: b ~> c) (g: a ~> b): splitmonic (f ∘ g) -> splitmonic g.
Proof.
  intros [h H].
  exists (h ∘ f).
  now rewrite <- comp_assoc.
Qed.

Lemma splitepic_comp_l {a b c: C} (f: b ~> c) (g: a ~> b): splitepic (f ∘ g) -> splitepic f.
Proof.
  intros [h H].
  exists (g ∘ h).
  now rewrite comp_assoc.
Qed.

End monoepi.

Module Isomorphism.

Structure mixin_of {C: Category} {x y: C} (f: x ~> y) := Mixin {
  inv: y ~> x;
  inv_l: inv ∘ f = id x;
  inv_r: f ∘ inv = id y;
}.

Notation class_of := mixin_of (only parsing).

Section ClassDef.
Context {C: Category} {x y: C}.

Structure type := Pack { morphism: x ~> y; _: class_of morphism }.
Local Coercion morphism: type >-> hom.

Variable (i: type).
Definition class := match i return class_of i with Pack _ c => c end.

End ClassDef.

Module Exports.

Arguments type {_} _ _.
Coercion morphism: type >-> hom.
Notation to := morphism.
Notation iso := type.

End Exports.

End Isomorphism.

Export Isomorphism.Exports.

Section iso.
Context {C: Category} {x y: C} (i: iso x y).

Definition from: y ~> x := Isomorphism.inv i (Isomorphism.class i).

Lemma from_to: from ∘ i = id x.
Proof. apply Isomorphism.inv_l. Qed.
Lemma to_from: i ∘ from = id y.
Proof. apply Isomorphism.inv_r. Qed.

Definition inv_mixin: Isomorphism.mixin_of from :=
  Isomorphism.Mixin _ _ _ from i to_from from_to.

Global Canonical inv: iso y x :=
  Isomorphism.Pack from inv_mixin.

Lemma inv_l: inv ∘ i = id x.
Proof. apply Isomorphism.inv_l. Qed.

Lemma inv_r: i ∘ inv = id y.
Proof. apply Isomorphism.inv_r. Qed.

End iso.

Infix "<~>" := iso (at level 70, no associativity).
Notation "i '⁻¹'" := (inv i) (at level 9).

Definition id_iso_mixin {C: Category} (x: C): Isomorphism.mixin_of (id x) :=
  Isomorphism.Mixin C x x (id x) (id x) (comp_id_l (id x)) (comp_id_l (id x)).

Canonical id_iso {C: Category} (x: C): x <~> x :=
  Isomorphism.Pack (id x) (id_iso_mixin x).

Section Comp_iso.
Context {C: Category} {x y z: C} (i: y <~> z) (j: x <~> y).

Lemma comp_inv_l: j⁻¹ ∘ i⁻¹ ∘ (i ∘ j) = id x.
Proof.
  rewrite comp_assoc.
  rewrite <- (comp_assoc (j⁻¹)).
  rewrite inv_l, comp_id_r.
  apply inv_l.
Qed.

Lemma comp_inv_r: i ∘ j ∘ (j⁻¹ ∘ i⁻¹) = id z.
Proof.
  rewrite comp_assoc.
  rewrite <- (comp_assoc i).
  rewrite inv_r, comp_id_r.
  apply inv_r.
Qed.

Definition iso_comp_mixin: Isomorphism.mixin_of (i ∘ j) :=
  Isomorphism.Mixin _ _ _ (i ∘ j) (j⁻¹ ∘ i⁻¹) comp_inv_l comp_inv_r.

Global Canonical iso_comp: iso x z :=
  Isomorphism.Pack (i ∘ j) iso_comp_mixin.

End Comp_iso.

Infix "·" := iso_comp (at level 40, left associativity).

Lemma iso_eq {C: Category} {x y: C} (i j: x <~> y): i = j <-> to i = to j.
Proof.
  split; intro H.
  now subst j.
  destruct i as [f [f' Hf1 Hf2]], j as [g [g' Hg1 Hg2]].
  simpl in H.
  subst g.
  f_equal.
  enough (f' = g').
  subst g'.
  f_equal.
  1, 2: apply proof_irrelevance.
  rewrite <- (comp_id_r f').
  rewrite <- Hg2.
  rewrite comp_assoc.
  rewrite Hf1.
  apply comp_id_l.
Qed.

Lemma icomp_assoc {C: Category} {a b c d: C} (f: c <~> d) (g: b <~> c) (h: a <~> b): f · (g · h) = (f · g) · h.
Proof.
  apply iso_eq; simpl.
  apply comp_assoc.
Qed.

Lemma icomp_id_l {C: Category} {x y: C} (i: x <~> y): id_iso y · i = i.
Proof.
  apply iso_eq; simpl.
  apply comp_id_l.
Qed.

Lemma icomp_id_r {C: Category} {x y: C} (i: x <~> y): i · id_iso x = i.
Proof.
  apply iso_eq; simpl.
  apply comp_id_r.
Qed.

Lemma icomp_inv_l {C: Category} {x y: C} (i: x <~> y): i⁻¹ · i = id_iso x.
Proof.
  apply iso_eq; simpl.
  apply from_to.
Qed.

Lemma icomp_inv_r {C: Category} {x y: C} (i: x <~> y): i · i⁻¹ = id_iso y.
Proof.
  apply iso_eq; simpl.
  apply to_from.
Qed.

Definition isomorphic (C: Category) (X Y: C) := inhabited (X <~> Y).

Infix "≃" := (isomorphic _) (at level 70).

Instance isomorphic_equiv C: Equivalence (isomorphic C).
Proof.
  constructor.
  + intros x.
    constructor.
    exact (id_iso x).
  + intros x y H.
    destruct H as [i].
    constructor.
    exact (i⁻¹).
  + intros x y z H H0.
    destruct H as [i], H0 as [j].
    constructor.
    eapply iso_comp; eassumption.
Qed.

Definition eq_iso {C: Category} {X Y: C} (e: X = Y): X <~> Y :=
  match e in (_ = y) return (X <~> y) with
  | eq_refl => id_iso X
  end.

Theorem eq_iso_refl {C: Category} {X: C} (e: X = X): eq_iso e = id_iso X.
Proof.
  unfold eq_iso.
  assert (e = eq_refl).
  apply proof_irrelevance.
  subst e.
  reflexivity.
Qed.

Definition is_iso {C: Category} {X Y: C} (f: X ~> Y) :=
  exists g: Y ~> X, g ∘ f = id X /\ f ∘ g = id Y.

Lemma is_iso_ex {C: Category} {X Y: C} (f: X ~> Y): is_iso f -> exists i: X <~> Y, to i = f.
Proof.
  intros [g [Hl Hr]].
  exists (Isomorphism.Pack f (Isomorphism.Mixin _ _ _ f g Hl Hr)).
  reflexivity.
Qed.

Lemma is_isomorphic {C: Category} {X Y: C} (f: X ~> Y): is_iso f -> X ≃ Y.
Proof.
  intros H.
  apply is_iso_ex in H.
  destruct H as [i H].
  constructor.
  exact i.
Qed.

Lemma is_iso_id {C: Category} {x: C}: is_iso (id x).
Proof.
  exists (id x).
  split.
  all: apply comp_id_l.
Qed.

Lemma is_iso_comp {C: Category} {X Y Z: C} (g: Y ~> Z) (f: X ~> Y): is_iso g -> is_iso f -> is_iso (g ∘ f).
Proof.
  intros [g' [Hgl Hgr]] [f' [Hfl Hfr]].
  exists (f' ∘ g'); split.
  all: rewrite comp_assoc.
  rewrite <- (comp_assoc f').
  rewrite Hgl, comp_id_r.
  apply Hfl.
  rewrite <- (comp_assoc g).
  rewrite Hfr, comp_id_r.
  apply Hgr.
Qed.

Definition is_eq {C: Category} {X Y: C} (f: X ~> Y) :=
  exists e: X = Y, f = eq_iso e.

Lemma iso_is_iso {C: Category} {X Y: C} (f: X <~> Y): is_iso f.
Proof.
  exists (f⁻¹).
  split.
  apply inv_l.
  apply inv_r.
Qed.

Lemma is_eq_is_iso {C: Category} {X Y: C} (f: X ~> Y): is_eq f -> is_iso f.
Proof.
  intros [e H].
  subst f.
  apply iso_is_iso.
Qed.

Lemma eq_iso_is_eq {C: Category} {X Y: C} (e: X = Y): is_eq (eq_iso e).
Proof. now exists e. Qed.

Lemma is_eq_refl {C: Category} {X: C} (η: X ~> X): is_eq η -> η = id X.
Proof.
  intros [e1 H1].
  subst η.
  now rewrite eq_iso_refl.
Qed.

Lemma is_eq_unique {C: Category} {X Y: C} (η ϵ: X ~> Y): is_eq η -> is_eq ϵ -> η = ϵ.
Proof.
  intros [e1 H1] [e2 H2].
  subst η ϵ.
  do 2 f_equal.
  apply proof_irrelevance.
Qed.

Lemma is_eq_unique_iso {C: Category} {X Y: C} (η ϵ: X <~> Y): is_eq η -> is_eq ϵ -> η = ϵ.
Proof.
  intros Hη Hϵ.
  now apply iso_eq, is_eq_unique.
Qed.

Lemma is_eq_id {C: Category} {X: C}: is_eq (id X).
Proof. now exists eq_refl. Qed.

Lemma is_eq_comp {C: Category} {X Y Z: C} (ϵ: Y ~> Z) (η: X ~> Y): is_eq η -> is_eq ϵ -> is_eq (ϵ ∘ η).
Proof.
  intros [e1 H1] [e2 H2].
  subst η ϵ Y Z.
  simpl.
  rewrite comp_id_l.
  apply is_eq_id.
Qed.

Lemma is_eq_inv {C: Category} {X Y: C} (η: X <~> Y): is_eq η -> is_eq η⁻¹.
Proof.
  intros [e H].
  apply iso_eq in H.
  subst η Y.
  apply is_eq_id.
Qed.

Theorem iso_is_splitmonic {C: Category} {x y: C} (i: x <~> y): splitmonic i.
Proof.
  exists (i⁻¹).
  apply inv_l.
Qed.

Theorem iso_is_splitepic {C: Category} {x y: C} (i: x <~> y): splitepic i.
Proof.
  exists (i⁻¹).
  apply inv_r.
Qed.

Theorem iso_monic {C: Category} {x y: C} (i: x <~> y): monic i.
Proof.
  apply splitmonic_is_monic.
  apply iso_is_splitmonic.
Qed.

Theorem iso_epic {C: Category} {x y: C} (i: x <~> y): epic i.
Proof.
  apply splitepic_is_epic.
  apply iso_is_splitepic.
Qed.

Theorem is_iso_is_splitmonic {C: Category} {x y: C} (f: x ~> y): is_iso f -> splitmonic f.
Proof.
  intros [f' [H _]].
  now exists (f').
Qed.

Theorem is_iso_is_splitepic {C: Category} {x y: C} (f: x ~> y): is_iso f -> splitepic f.
Proof.
  intros [f' [_ H]].
  now exists (f').
Qed.

Theorem is_iso_monic {C: Category} {x y: C} (f: x ~> y): is_iso f -> monic f.
Proof.
  intros H.
  apply splitmonic_is_monic, is_iso_is_splitmonic, H.
Qed.

Theorem is_iso_epic {C: Category} {x y: C} (f: x ~> y): is_iso f -> epic f.
Proof.
  intros H.
  apply splitepic_is_epic, is_iso_is_splitepic, H.
Qed.

Theorem splitmonic_epic {C: Category} {x y: C} (f: x ~> y): splitmonic f -> epic f -> is_iso f.
Proof.
  intros [g inv_l] H.
  exists g; split.
  exact inv_l.
  apply H.
  rewrite <- comp_assoc, comp_id_l.
  rewrite inv_l.
  apply comp_id_r.
Qed.

Theorem splitepic_monic {C: Category} {x y: C} (f: x ~> y): splitepic f -> monic f -> is_iso f.
Proof.
  intros [g inv_r] H.
  exists g; split.
  apply H.
  rewrite comp_assoc, comp_id_r.
  rewrite inv_r.
  apply comp_id_l.
  exact inv_r.
Qed.

Theorem is_iso_comp_l {C: Category} {x y z: C} (f: y ~> z) (g: x ~> y): is_iso (f ∘ g) -> is_iso g -> is_iso f.
Proof.
  intros [c Hc] [g' Hg].
  exists (g ∘ c); split.
  rewrite <- (comp_id_r _).
  rewrite <- (proj2 Hg).
  rewrite <- !(comp_assoc g).
  f_equal.
  rewrite comp_assoc, <- (comp_assoc c).
  rewrite (proj1 Hc).
  apply comp_id_l.
  now rewrite comp_assoc.
Qed.

Theorem is_iso_comp_r {C: Category} {x y z: C} (f: y ~> z) (g: x ~> y): is_iso (f ∘ g) -> is_iso f -> is_iso g.
Proof.
  intros [c Hc] [f' Hf].
  exists (c ∘ f); split.
  now rewrite <- comp_assoc.
  rewrite <- (comp_id_l _).
  rewrite <- (proj1 Hf).
  rewrite <- comp_assoc.
  f_equal.
  rewrite !comp_assoc.
  rewrite (proj2 Hc).
  apply comp_id_l.
Qed.

Definition co_iso_mixin {C: Category} {x y: C} (i: x <~> y): Isomorphism.mixin_of (from i: @hom (co C) x y) :=
  Isomorphism.Mixin (co C) x y (from i) (to i) (from_to i) (to_from i).

Definition co_iso {C: Category} {x y: C} (i: x <~> y): (x: co C) <~> y :=
  Isomorphism.Pack _ (co_iso_mixin i).

Definition co_iso_mixin' {C: Category} {x y: C} (i: (x: co C) <~> y): Isomorphism.mixin_of (from i: x ~> y) :=
  Isomorphism.Mixin C x y (from i) (to i) (from_to i) (to_from i).

Definition co_iso' {C: Category} {x y: C} (i: (x: co C) <~> y): x <~> y :=
  Isomorphism.Pack _ (co_iso_mixin' i).

Theorem iso_co {C: Category} (x y: C): (x: co C) ≃ y <-> x ≃ y.
  split.
  + intros [i].
    constructor.
    apply co_iso', i.
  + intros [i].
    constructor.
    apply co_iso, i.
Qed.

Lemma is_iso_co {C: Category} {x y: C} (f: x ~> y): is_iso (f: (y: co C) ~> x) <-> is_iso f.
Proof.
  split.
  all: intros [g [Hl Hr]].
  all: exists g; split.
  1, 3: exact Hr.
  all: exact Hl.
Qed.

Lemma is_iso_co' {C: Category} {x y: C} (f: (x: co C) ~> y): is_iso (f: y ~> x) <-> is_iso f.
Proof.
  split.
  all: intros [g [Hl Hr]].
  all: exists g; split.
  1, 3: exact Hr.
  all: exact Hl.
Qed.

Lemma monic_co {C: Category} {x y: C} (f: x ~> y): monic f <-> epic (f: (y: co C) ~> x).
Proof. reflexivity. Qed.

Lemma epic_co {C: Category} {x y: C} (f: x ~> y): epic f <-> monic (f: (y: co C) ~> x).
Proof. reflexivity. Qed.

Lemma monic_co' {C: Category} {x y: C} (f: (x: co C) ~> y): monic (f: y ~> x) <-> epic f.
Proof. reflexivity. Qed.

Lemma epic_co' {C: Category} {x y: C} (f: (x: co C) ~> y): epic (f: y ~> x) <-> monic f.
Proof. reflexivity. Qed.

Lemma splitmonic_co {C: Category} {x y: C} (f: x ~> y): splitmonic f <-> splitepic (f: (y: co C) ~> x).
Proof. reflexivity. Qed.

Lemma splitepic_co {C: Category} {x y: C} (f: x ~> y): splitepic f <-> splitmonic (f: (y: co C) ~> x).
Proof. reflexivity. Qed.

Lemma splitmonic_co' {C: Category} {x y: C} (f: (x: co C) ~> y): splitmonic (f: y ~> x) <-> splitepic f.
Proof. reflexivity. Qed.

Lemma splitepic_co' {C: Category} {x y: C} (f: (x: co C) ~> y): splitepic (f: y ~> x) <-> splitmonic f.
Proof. reflexivity. Qed.

Lemma is_eq_co {C: Category} {x y: C} (f: x ~> y): is_eq f -> is_eq (f: (y: co C) ~> x).
Proof.
  intros [e H].
  subst f y.
  exact is_eq_id.
Qed.

Lemma co_eq_iso {C: Category} {x y: C} (e: x = y): to (@eq_iso (co C) x y e) = to (eq_iso e)⁻¹.
Proof. now destruct e. Qed.
