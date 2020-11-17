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

Lemma Yoneda_lemma (C: Category) (c: C) (P: Fun (co C) Typ): Hom (Fun (co C) Typ) (よ C c, P) ≃ P c.
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
