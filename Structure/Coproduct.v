Require Export Base.

Definition is_coproduct {C: Category} (a b p: C) (p1: a ~> p) (p2: b ~> p) :=
  forall (z: C) (f: a ~> z) (g: b ~> z), exists! h: p ~> z, h ∘ p1 = f /\ h ∘ p2 = g.

Definition is_coprod_obj {C: Category} (a b p: C) :=
  exists (p1: a ~> p) (p2: b ~> p), is_coproduct a b p p1 p2.

Definition ex_coproduct {C: Category} (a b: C) :=
  exists (p: C), is_coprod_obj a b p.

Instance is_coprod_obj_iso (C: Category): Proper (isomorphic C ==> isomorphic C ==> isomorphic C ==> iff) is_coprod_obj.
Proof.
  enough (Proper (isomorphic C ==> isomorphic C ==> isomorphic C ==> impl) is_coprod_obj).
  now split; apply H.
  intros a x [i] b y [j] p q [k] [p1 [p2 H]].
  exists (k ∘ p1 ∘ i⁻¹), (k ∘ p2 ∘ j⁻¹).
  intros z f' g'.
  assert (exists f: a ~> z, f ∘ i⁻¹ = f').
    exists (f' ∘ i).
    rewrite <- comp_assoc, inv_r.
    apply comp_id_r.
  destruct H0 as [f].
  subst f'.
  assert (exists g: b ~> z, g ∘ j⁻¹ = g').
    exists (g' ∘ j).
    rewrite <- comp_assoc, inv_r.
    apply comp_id_r.
  destruct H0 as [g].
  subst g'.
  specialize (H z f g).
  destruct H as [h [[H1 H2] Hh]].
  subst f g.
  exists (h ∘ k⁻¹).
  repeat split.
  1, 2: rewrite !comp_assoc.
  1, 2: do 2 f_equal.
  1, 2: rewrite <- comp_assoc, inv_l.
  1, 2: apply comp_id_r.
  intros h' [H1 H2].
  rewrite !comp_assoc in H1.
  rewrite !comp_assoc in H2.
  apply iso_epic in H1.
  apply iso_epic in H2.
  apply (iso_epic k).
  rewrite <- comp_assoc, inv_l, comp_id_r.
  now apply Hh.
Qed.

Instance ex_coproduct_iso (C: Category): Proper (isomorphic C ==> isomorphic C ==> iff) ex_coproduct.
Proof.
  intros a x H1 b y H2.
  unfold ex_coproduct.
  f_equiv.
  intros p.
  now f_equiv.
Qed.

Lemma coprod_obj_euniqueness {C: Category} (a b: C): euniqueness (is_coprod_obj a b).
Proof.
  intros p q [p1 [p2 Hp]] [q1 [q2 Hq]].
  destruct (Hq p p1 p2) as [f [Hf _]].
  destruct (Hp q q1 q2) as [g [Hg _]].
  constructor.
  exists g, f.
  all: symmetry.
  + specialize (Hp p p1 p2).
    destruct Hp as [p' [Hp H]].
    transitivity p'.
    symmetry.
    all: apply H.
    all: split.
    1, 2: apply comp_id_l.
    all: rewrite <- comp_assoc.
    now rewrite (proj1 Hg).
    now rewrite (proj2 Hg).
  + specialize (Hq q q1 q2).
    destruct Hq as [q' [Hq H]].
    transitivity q'.
    symmetry.
    all: apply H.
    all: split.
    1, 2: apply comp_id_l.
    all: rewrite <- comp_assoc.
    now rewrite (proj1 Hf).
    now rewrite (proj2 Hf).
Qed.

Lemma ex_coproduct_eunique {C: Category} (a b: C): ex_coproduct a b <-> exists!! p, is_coprod_obj a b p.
Proof.
  rewrite <- eunique_existence.
  split.
  + intros H.
    split.
    now apply is_coprod_obj_iso.
    split.
    exact H.
    apply coprod_obj_euniqueness.
  + intros [_ [H _]].
    exact H.
Qed.

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

Lemma merge_fcoprod {a a' b b' c} (f: b ~> c) (f': b' ~> c) (g: a ~> b) (g': a' ~> b'): [f, f'] ∘ (g (+) g') = [f ∘ g, f' ∘ g'].
Proof.
  unfold fcoprod.
  rewrite merge_comp.
  f_equal.
  all: rewrite comp_assoc.
  all: f_equal.
  apply merge_in1.
  apply merge_in2.
Qed.

Lemma fcoprod_comp {a a' b b' c c': C} (f: b ~> c) (f': b' ~> c') (g: a ~> b) (g': a' ~> b'): (f (+) f') ∘ (g (+) g') = (f ∘ g) (+) (f' ∘ g').
Proof.
  unfold fcoprod at 2 3.
  rewrite !comp_assoc.
  apply merge_fcoprod.
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

Lemma in_is_coproduct (a b: C): is_coproduct a b (a + b) in1 in2.
Proof.
  intros z f g.
  exists [f, g].
  repeat split.
  apply merge_in1.
  apply merge_in2.
  intros h H.
  symmetry.
  now apply merge_in.
Qed.

Lemma coprod_is_coprod_obj (a b: C): is_coprod_obj a b (a + b).
Proof.
  exists in1, in2.
  apply in_is_coproduct.
Qed.

End Coproduct.

Infix "+" := coprod (at level 50, left associativity).
Infix "(+)" := fcoprod (at level 50, left associativity).
Notation "[ f , g ]" := (merge f g).
Canonical icoprod.

Lemma coproduct_correct C: inhabited (CoprodCategory.mixin_of C) <-> (forall a b: C, ex_coproduct a b).
Proof.
  split.
  + intros [[p merge i1 i2 H]] a b.
    exists (p a b), (i1 a b), (i2 a b).
    intros z f g.
    exists (merge a b z f g); split.
    now apply H.
    intros h Hh.
    symmetry.
    now apply H.
  + intros H.
    generalize (fun a => ex_forall _ (H a)).
    clear H; intros H.
    apply ex_forall in H.
    destruct H as [P H].
    generalize (fun a => ex_forall _ (H a)).
    clear H; intros H.
    apply ex_forall in H.
    destruct H as [i1 H].
    generalize (fun a => ex_forall _ (H a)).
    clear H; intros H.
    apply ex_forall in H.
    destruct H as [i2 H].
    generalize (fun a b z f => ex_forall _ (H a b z f)).
    clear H; intros H.
    generalize (fun a b z => ex_forall _ (H a b z)).
    clear H; intros H.
    generalize (fun a b => ex_forall _ (H a b)).
    clear H; intros H.
    generalize (fun a => ex_forall _ (H a)).
    clear H; intros H.
    apply ex_forall in H.
    destruct H as [m H].
    constructor.
    exists P m i1 i2.
    intros a b c f g h.
    specialize (H a b c f g).
    destruct H as [H u].
    split.
    intros Hh.
    now subst h.
    intros Hh.
    symmetry.
    now apply u.
Qed.
