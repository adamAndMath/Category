Require Export Base.

Definition is_proset (C: Category) :=
  forall (x y: C) (f g: x ~> y), f = g.

Definition is_directed (C: Category) :=
  forall x y: C, x ~> y -> y ~> x -> x = y.

Definition is_poset (C: Category) :=
  is_proset C /\ is_directed C.

Definition connected {C: Category} (x y: C) := inhabited (x ~> y).

Instance connected_preorder (C: Category): PreOrder (@connected C).
Proof.
  split; red; intros.
  + constructor.
    exact (id x).
  + destruct H as [f], H0 as [g].
    constructor.
    exact (g ∘ f).
Qed.

Definition connected_partialorder (C: Category): is_directed C <-> PartialOrder eq (@connected C).
Proof.
  split.
  + intros H x y.
    split.
    intros Hx.
    now subst y.
    intros [[f] [g]].
    now apply H.
  + intros H x y f g.
    apply H.
    split.
    all: now constructor.
Qed.

Module Proset.

Section category.
Context {T} (R: T -> T -> Prop) {pre: PreOrder R}.

Definition cat_mixin: Category.mixin_of T :=
  Category.Mixin T R reflexivity (fun _ _ _ f g => transitivity g f)
  (fun _ _ _ _ _ _ _ => proof_irrelevance _ _ _)
  (fun _ _ _ => proof_irrelevance _ _ _)
  (fun _ _ _ => proof_irrelevance _ _ _).

Definition cat: Category :=
  Category.Pack T cat_mixin.

Lemma hom_eq {x y: cat} (f g: x ~> y): f = g.
Proof.
  simpl in *.
  unfold hom in f, g.
  simpl in *.
  assert (f = g).
  apply proof_irrelevance.
  exact H.
Qed.

End category.

End Proset.

Notation Proset := Proset.cat.

Definition Poset {T} (R: T -> T -> Prop) {pre: PreOrder R} {po: PartialOrder eq R} := Proset R.

Lemma Proset_correct {T} (R: T -> T -> Prop) {pre: PreOrder R}: is_proset (Proset R).
Proof.
  intros x y f g.
  red in f, g.
  simpl in f, g.
  now assert (f = g) by apply proof_irrelevance.
Qed.

Lemma Poset_correct {T} (R: T -> T -> Prop) {pre: PreOrder R} {po: PartialOrder eq R}: is_poset (Poset R).
Proof.
  split.
  apply Proset_correct.
  intros x y f g.
  now apply po.
Qed.

Lemma proset_ex (C: Category): is_proset C -> Proset (@connected C) ≃ C.
Proof.
  intros H.
  assert (inhabited (forall (x y: C) (f: @hom (Proset connected) x y), x ~> y)).
    apply inhabit_forall.
    intros x.
    apply inhabit_forall.
    intros y.
    apply inhabit_forall.
    intros f.
    exact f.
  destruct H0 as [F].
  constructor.
  1: unshelve eexists.
  2: unshelve eexists.
  1: exists (fun x: Proset connected => x: C) F.
  3: exists (fun x: C => x: Proset connected) (fun x y => @inhabits (x ~> y)).
  5, 6: fun_eq x y f.
  all: intros.
  all: first[apply H | apply Proset.hom_eq].
Qed.

Lemma dual_proset {T} (R: T -> T -> Prop) {pre: PreOrder R}: co (Proset R) = Proset (flip R).
Proof.
  unfold co, Proset; simpl.
  f_equal.
  apply cat_mixin_eq; simpl.
  repeat split.
  intros x e.
  apply proof_irrelevance.
  intros x y z f g e1 e2 e3.
  apply proof_irrelevance.
Qed.

Lemma dual_poset {T} (R: T -> T -> Prop) {pre: PreOrder R} {po: PartialOrder eq R}: co (Poset R) = @Poset _ (flip R) _ (PartialOrder_inverse po).
Proof. apply dual_proset. Qed.
