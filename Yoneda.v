Require Export Categories.Typ.

Program Definition Yoneda (C: Category): Functor C (Fun (co C) Typ) := {|
  fobj A := {|
    fobj X := @hom C X A;
    fmap X Y f g := @comp C _ _ _ g f;
  |};
  fmap A B f := {|
    transform X g := f ∘ g;
  |}
|}.
Next Obligation.
  extensionality f.
  apply (@comp_id_r C).
Qed.
Next Obligation.
  extensionality h.
  apply (@comp_assoc C).
Qed.
Next Obligation.
  extensionality g.
  apply comp_assoc.
Qed.
Next Obligation.
  natural_eq x.
  extensionality f.
  apply comp_id_l.
Qed.
Next Obligation.
  natural_eq x.
  extensionality h.
  symmetry.
  apply comp_assoc.
Qed.

Notation よ := Yoneda.

Lemma Yoneda_lemma {C: Category} (c: C) (P: Fun (co C) Typ): Hom (Fun (co C) Typ) (よ C c, P) ≃ P c.
Proof.
  constructor.
  unshelve eexists.
  exact (fun η => η c (id c)).
  unshelve eexists.
  intros x.
  unshelve eexists.
  exact (fun d f => fmap P f x).
  2: extensionality η.
  3: extensionality x.
  2, 3: unfold comp, id; simpl.
  2: natural_eq x.
  2: extensionality f.
  + intros b a f.
    simpl in a, b.
    change (a ~> b) in f.
    extensionality g.
    change (fmap P (g ∘ f) x = (fmap P f ∘ fmap P g) x).
    apply (f_equal (fun f => f x)).
    apply (@fmap_comp _ _ P).
  + change (よ C c ~> P) in η.
    specialize (@naturality _ _ _ _ η c x f) as H.
    apply (f_equal (fun f => f (id c))) in H.
    unfold comp in H; simpl in H.
    rewrite comp_id_l in H.
    now symmetry.
  + change (fmap P (id c) x = id (P c) x).
    apply (f_equal (fun f => f x)).
    apply (@fmap_id _ _ P).
Qed.

Lemma Yoneda_full (C: Category): full (よ C).
Proof.
  intros x y η.
  exists (η x (id x)).
  natural_eq z.
  extensionality f.
  specialize (@naturality _ _ _ _ η x z f) as H.
  simpl in H.
  unfold comp at 1 5 in H; simpl in H.
  apply (f_equal (fun f => f (id x))) in H.
  symmetry.
  rewrite <- (comp_id_l f) at 1.
  exact H.
Qed.

Lemma Yoneda_faithful (C: Category): faithful (よ C).
Proof.
  intros x y f g H.
  generalize (proj1 (natural_eq _ _) H).
  clear H; intros H.
  simpl in H.
  specialize (H x).
  apply (f_equal (fun f => f (id x))) in H.
  now rewrite !comp_id_r in H.
Qed.

Lemma Yoneda_fully_faithful (C: Category): fully_faithful (よ C).
Proof.
  apply full_and_faithful.
  split.
  apply Yoneda_full.
  apply Yoneda_faithful.
Qed.

(* fully_faithful_iso is currently to strict in its universes *)
Lemma Yoneda_principle {C: Category} (A B: C): よ C A ≃ よ C B <-> A ≃ B.
Proof.
  split.
  + intros [η].
    constructor.
    exists (to η A (id A)),  (to η⁻¹ B (id B)).
    specialize (@naturality _ _ _ _ (to η⁻¹) B A (to η A (id A))) as H.
    apply (f_equal (fun f => f (id B))) in H.
    unfold comp in H; simpl in H.
    change (from ?i) with (to i⁻¹) in H.
    etransitivity.
    symmetry.
    exact H.
    rewrite comp_id_l.
    change ((η⁻¹ ∘ η) A (id A) = id (よ C A) A (id A)).
    f_equal.
    apply inv_l.
    specialize (@naturality _ _ _ _ (to η) A B (to η⁻¹ B (id B))) as H.
    apply (f_equal (fun f => f (id A))) in H.
    unfold comp in H; simpl in H.
    change (from ?i) with (to i⁻¹) in H.
    etransitivity.
    symmetry.
    exact H.
    rewrite comp_id_l.
    change ((η ∘ η⁻¹) B (id B) = id (よ C B) B (id B)).
    f_equal.
    apply inv_r.
  + intros [f].
    constructor.
    1: unshelve eexists.
    2: unshelve eexists.
    1: exists (fun Z g => f ∘ g).
    2: exists (fun Z g => f⁻¹ ∘ g).
    3, 4: natural_eq Z.
    1, 2: intros Y X g.
    1, 2: simpl in Y, X.
    1, 2: change (X ~> Y) in g.
    all: extensionality h.
    all: simpl in h.
    1, 2: unfold comp at 1 3; simpl.
    3, 4: unfold comp at 1, id; simpl.
    all: change (from ?i) with (to i⁻¹).
    1, 2: apply comp_assoc.
    all: rewrite comp_assoc, <- comp_id_l.
    all: f_equal.
    apply inv_l.
    apply inv_r.
Qed.
