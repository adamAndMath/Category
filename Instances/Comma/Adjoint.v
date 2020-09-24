Require Export Typ.
Require Export Comma.

Program Definition Comma2Prod {A B C: Category} (F: A ~> C) (G: B ~> C): F ↓ G ~> A × B := {|
  fobj x := (Comma.source x, Comma.target x);
  fmap _ _ f := (Comma.smap f, Comma.tmap f);
|}.

Lemma Comma2Prod_is_SourceTarget {A B C: Category} (F: A ~> C) (G: B ~> C): ⟨Comma.Source, Comma.Target⟩ = Comma2Prod F G.
Proof.
  fun_eq x y f.
  rewrite !eq_iso_refl.
  simpl.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Section Adjoint_Comma.
Context {C D: Category} (F: C ~> D) (G: D ~> C).

Section Adjoint2Comma.
Context (φ: Typ.Hom D ∘ ⟨cof F ∘ π₁, π₂⟩ <~> Typ.Hom C ∘ ⟨π₁, G ∘ π₂⟩).

Program Definition comma_to: F ↓ id D ~> id C ↓ G := {|
  fobj x := {|
    Comma.source := Comma.source x;
    Comma.target := Comma.target x;
    Comma.morph := to φ (Comma.source x, Comma.target x) (Comma.morph x);
  |};
  fmap a b f := {|
    Comma.smap := Comma.smap f;
    Comma.tmap := Comma.tmap f;
  |};
|}.
Next Obligation.
  specialize (@naturality _ _ _ _ (to φ) (Comma.source a, Comma.target a) (Comma.source a, Comma.target b) (id (Comma.source a), Comma.tmap f)) as H.
  apply (f_equal (fun f => f (Comma.morph a))) in H.
  unfold comp in H.
  simpl in H.
  unfold tcomp in H.
  rewrite fmap_id, !comp_id_r in H.
  etransitivity.
  symmetry.
  exact H.
  clear H.
  specialize (Comma.comm _ _ _ _ f) as e.
  simpl in e.
  rewrite e; clear e.
  specialize (proj1 (natural_eq _ _) (inv_r φ) (Comma.source a, Comma.target b)) as H.
  apply (f_equal (fun g => g (to φ (Comma.source b, Comma.target b) (Comma.morph b) ∘ Comma.smap f))) in H.
  unfold comp, id in H; simpl in H.
  unfold comp, id in H; simpl in H.
  unfold tcomp, tid in H.
  change (Category.comp (Category.obj ?C) _ ?f ?g) with (@comp C _ _ _ f g) in H.
  etransitivity.
  2: exact H.
  clear H.
  f_equal.
  specialize (proj1 (natural_eq _ _) (inv_l φ) (Comma.source b, Comma.target b)) as H.
  apply (f_equal (fun g => g (Comma.morph b))) in H.
  unfold comp, id in H; simpl in H.
  unfold comp, id in H; simpl in H.
  unfold tcomp, tid in H.
  etransitivity.
  apply (f_equal (fun f => f ∘ _)).
  symmetry.
  exact H.
  clear H.
  set (g := to φ (Comma.source b, Comma.target b) (Comma.morph b)).
  change (to φ⁻¹ (Comma.source b, Comma.target b) g ∘ fmap F (Comma.smap f) = to φ⁻¹ (Comma.source a, Comma.target b) (g ∘ Comma.smap f)).
  specialize (@ naturality _ _ _ _ (to φ⁻¹) (Comma.source b, Comma.target b) (Comma.source a, Comma.target b) (Comma.smap f, id (Comma.target b))) as H.
  apply (f_equal (fun f => f g)) in H.
  unfold comp in H; simpl in H.
  unfold tcomp in H.
  rewrite fmap_id, !comp_id_l in H.
  symmetry.
  exact H.
Qed.
Next Obligation.
  now apply Comma.hom_eq.
Qed.
Next Obligation.
  now apply Comma.hom_eq.
Qed.

Program Definition comma_from: id C ↓ G ~> F ↓ id D := {|
  fobj x := {|
    Comma.source := Comma.source x;
    Comma.target := Comma.target x;
    Comma.morph := to φ⁻¹ (Comma.source x, Comma.target x) (Comma.morph x);
  |};
  fmap a b f := {|
    Comma.smap := Comma.smap f;
    Comma.tmap := Comma.tmap f;
  |};
|}.
Next Obligation.
  specialize (@naturality _ _ _ _ (to φ⁻¹) (Comma.source b, Comma.target b) (Comma.source a, Comma.target b) (Comma.smap f, id (Comma.target b))) as H.
  apply (f_equal (fun f => f (Comma.morph b))) in H.
  unfold comp in H.
  simpl in H.
  unfold tcomp in H.
  rewrite fmap_id, !comp_id_l in H.
  etransitivity.
  2: exact H.
  clear H.
  specialize (Comma.comm _ _ _ _ f) as e.
  simpl in e.
  rewrite <- e; clear e.
  specialize (proj1 (natural_eq _ _) (inv_l φ) (Comma.source a, Comma.target b)) as H.
  apply (f_equal (fun g => g (Comma.tmap f ∘ to φ⁻¹ (Comma.source a, Comma.target a) (Comma.morph a)))) in H.
  unfold comp, id in H; simpl in H.
  unfold comp, id in H; simpl in H.
  unfold tcomp, tid in H.
  change (Category.comp (Category.obj ?C) _ ?f ?g) with (@comp C _ _ _ f g) in H.
  etransitivity.
  symmetry.
  exact H.
  clear H.
  f_equal.
  specialize (proj1 (natural_eq _ _) (inv_r φ) (Comma.source a, Comma.target a)) as H.
  apply (f_equal (fun f => f (Comma.morph a))) in H.
  unfold comp, id in H; simpl in H.
  unfold comp, id in H; simpl in H.
  unfold tcomp, tid in H.
  etransitivity.
  2: apply f_equal.
  2: exact H.
  clear H.
  set (g := to φ⁻¹ (Comma.source a, Comma.target a) (Comma.morph a)).
  change (to φ (Comma.source a, Comma.target b) (Comma.tmap f ∘ g) = fmap G (Comma.tmap f) ∘ to φ (Comma.source a, Comma.target a) g).
  specialize (@ naturality _ _ _ _ (to φ) (Comma.source a, Comma.target a) (Comma.source a, Comma.target b) (id (Comma.source a), Comma.tmap f)) as H.
  apply (f_equal (fun f => f g)) in H.
  unfold comp in H; simpl in H.
  unfold tcomp in H.
  rewrite fmap_id, !comp_id_r in H.
  exact H.
Qed.
Next Obligation.
  now apply Comma.hom_eq.
Qed.
Next Obligation.
  now apply Comma.hom_eq.
Qed.

Lemma comma_inv_l: comma_from ∘ comma_to = id (F ↓ id D).
Proof.
  fun_eq x y f.
  apply Comma.obj_eq; simpl.
  repeat split.
  intros Hs Ht.
  rewrite !eq_iso_refl.
  clear Hs Ht.
  simpl.
  rewrite fmap_id, comp_id_l, comp_id_r.
  specialize (proj1 (natural_eq _ _) (inv_l φ) (Comma.source x, Comma.target x)) as H.
  apply (f_equal (fun f => f (Comma.morph x))) in H.
  unfold comp, id in H; simpl in H.
  unfold comp, id in H; simpl in H.
  unfold tcomp, tid in H.
  exact H.
  apply Comma.hom_eq; simpl.
  split.
  all: etransitivity.
  1, 3: apply (f_equal (fun f => f ∘ _)).
  1, 2: apply is_eq_refl.
  1, 2: destruct H0.
  1, 2: apply is_eq_id.
  all: rewrite comp_id_l.
  1: rewrite <- (comp_id_r (Comma.smap f)) at 1.
  2: rewrite <- (comp_id_r (Comma.tmap f)) at 1.
  all: f_equal.
  all: symmetry.
  all: apply is_eq_refl.
  all: destruct H.
  all: apply is_eq_id.
Qed.

Lemma comma_inv_r: comma_to ∘ comma_from = id (id C ↓ G).
Proof.
  fun_eq x y f.
  apply Comma.obj_eq; simpl.
  repeat split.
  intros Hs Ht.
  rewrite !eq_iso_refl.
  clear Hs Ht.
  simpl.
  rewrite fmap_id, comp_id_l, comp_id_r.
  specialize (proj1 (natural_eq _ _) (inv_r φ) (Comma.source x, Comma.target x)) as H.
  apply (f_equal (fun f => f (Comma.morph x))) in H.
  unfold comp, id in H; simpl in H.
  unfold comp, id in H; simpl in H.
  unfold tcomp, tid in H.
  exact H.
  apply Comma.hom_eq; simpl.
  split.
  all: etransitivity.
  1, 3: apply (f_equal (fun f => f ∘ _)).
  1, 2: apply is_eq_refl.
  1, 2: destruct H0.
  1, 2: apply is_eq_id.
  all: rewrite comp_id_l.
  1: rewrite <- (comp_id_r (Comma.smap f)) at 1.
  2: rewrite <- (comp_id_r (Comma.tmap f)) at 1.
  all: f_equal.
  all: symmetry.
  all: apply is_eq_refl.
  all: destruct H.
  all: apply is_eq_id.
Qed.

Definition comma_iso: F ↓ id D <~> id C ↓ G :=
  Isomorphism.Pack comma_to (Isomorphism.Mixin _ _ _ comma_to comma_from comma_inv_l comma_inv_r).

Lemma comma_iso_correct: Comma2Prod (id C) G ∘ comma_iso = Comma2Prod F (id D).
Proof.
  fun_eq x y f.
  rewrite !eq_iso_refl.
  clear H H0.
  simpl.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

End Adjoint2Comma.

Lemma adjoint2comma: F -| G -> exists φ: F ↓ id D <~> id C ↓ G, Comma2Prod (id C) G ∘ φ = Comma2Prod F (id D).
Proof.
  intros H.
  apply adjoint_hom in H.
  destruct H as [φ].
  exists (comma_iso φ).
  exact (comma_iso_correct φ).
Qed.

Lemma comma2adjoint(φ: F ↓ id D <~> id C ↓ G): Comma2Prod (id C) G ∘ φ = Comma2Prod F (id D) -> F -| G.
Proof.
  intros Hφ.
  apply adjoint_hom.
  destruct φ as [φ [θ]].
  simpl in Hφ.
  destruct φ as [φo φf φ_id φ_comp].
  destruct θ as [θo θf θ_id θ_comp].
  assert (exists (φs: F ↓ id D -> C) (φt: F ↓ id D -> D) (φ': forall x: F ↓ id D, id C (φs x) ~> G (φt x)),
    (fun x: F ↓ id D => Comma.Obj (id C) G (φs x) (φt x) (φ' x)) = φo
  ).
  1: {
    exists (fun x => Comma.source (φo x)).
    exists (fun x => Comma.target (φo x)).
    exists (fun x => Comma.morph (φo x)).
    extensionality x.
    now destruct (φo x).
  }
  assert (exists (θs: id C ↓ G -> C) (θt: id C ↓ G -> D) (θ': forall x: id C ↓ G, F (θs x) ~> id D (θt x)),
    (fun x: id C ↓ G => Comma.Obj F (id D) (θs x) (θt x) (θ' x)) = θo
  ).
  1: {
    exists (fun x => Comma.source (θo x)).
    exists (fun x => Comma.target (θo x)).
    exists (fun x => Comma.morph (θo x)).
    extensionality x.
    now destruct (θo x).
  }
  destruct H as [φs [φt [φ H]]].
  destruct H0 as [θs [θt [θ H0]]].
  subst φo θo.
  assert (φs = Comma.source /\ φt = Comma.target).
  1: {
    apply fun_eq, proj1 in Hφ.
    simpl in Hφ.
    split.
    all: extensionality x.
    all: specialize (Hφ x).
    all: now injection Hφ.
  }
  destruct H.
  subst φs φt.
  assert (θs = Comma.source /\ θt = Comma.target).
  1: {
    apply fun_eq, proj1 in inv_r.
    simpl in inv_r.
    split.
    all: extensionality x.
    all: specialize (inv_r x).
    all: destruct x as [xs xt x].
    all: simpl in inv_r |- *.
    now apply (f_equal Comma.source) in inv_r.
    now apply (f_equal Comma.target) in inv_r.
  }
  destruct H.
  subst θs θt.
  assert (exists φ': forall x y, F x ~> y -> x ~> G y, (fun x: F ↓ id D => φ' (Comma.source x) (Comma.target x) (Comma.morph x)) = φ).
  1: {
    exists (fun x y f => φ (Comma.Obj F (id D) x y f)).
    extensionality x.
    now destruct x.
  }
  assert (exists θ': forall x y, x ~> G y -> F x ~> y, (fun x: id C ↓ G => θ' (Comma.source x) (Comma.target x) (Comma.morph x)) = θ).
  1: {
    exists (fun x y f => θ (Comma.Obj (id C) G x y f)).
    extensionality x.
    now destruct x.
  }
  destruct H as [φ' H], H0 as [θ' H0].
  subst φ θ.
  assert (exists φs φt Hφf, (fun a b f => Comma.Hom (id C) G _ _ (φs a b f) (φt a b f) (Hφf a b f)) = φf).
  1: {
    exists (fun a b f => Comma.smap (φf a b f)).
    exists (fun a b f => Comma.tmap (φf a b f)).
    simpl.
    unshelve eexists.
    intros a b f.
    apply (Comma.comm _ _ _ _ (φf a b f)).
    extensionality a.
    extensionality b.
    extensionality f.
    now apply Comma.hom_eq.
  }
  destruct H as [φs [φt [Hφf H]]].
  subst φf.
  assert (exists θs θt Hθf, (fun a b f => Comma.Hom F (id D) _ _ (θs a b f) (θt a b f) (Hθf a b f)) = θf).
  1: {
    exists (fun a b f => Comma.smap (θf a b f)).
    exists (fun a b f => Comma.tmap (θf a b f)).
    simpl.
    unshelve eexists.
    intros a b f.
    apply (Comma.comm _ _ _ _ (θf a b f)).
    extensionality a.
    extensionality b.
    extensionality f.
    now apply Comma.hom_eq.
  }
  destruct H as [θs [θt [Hθf H]]].
  subst θf.
  simpl in φs, φt, θs, θt.
  assert ((fun x y => Comma.smap) = φs /\ (fun x y => Comma.tmap) = φt).
  1: {
    clear - Hφ.
    apply fun_eq, proj2 in Hφ.
    simpl in Hφ.
    clear - Hφ.
    specialize (fun x y f => Hφ x y f eq_refl eq_refl).
    simpl in Hφ.
    split.
    all: extensionality x.
    all: extensionality y.
    all: extensionality f.
    all: specialize (Hφ x y f).
    all: rewrite comp_id_l, comp_id_r in Hφ.
    all: now injection Hφ.
  }
  destruct H.
  subst φs φt.
  clear Hφ.
  assert ((fun x y => Comma.smap) = θs /\ (fun x y => Comma.tmap) = θt).
  1: {
    apply fun_eq in inv_r.
    simpl in inv_r.
    clear - inv_r.
    destruct inv_r as [H H0].
    split.
    all: extensionality x.
    all: extensionality y.
    all: extensionality f.
    all: specialize (H x) as Hx.
    all: specialize (H y) as Hy.
    all: specialize (H0 x y f) as Hf.
    all: clear H H0.
    all: specialize (Hf Hx Hy).
    1: apply (f_equal Comma.smap) in Hf.
    2: apply (f_equal Comma.tmap) in Hf.
    all: simpl in Hf.
    1: rewrite <- (comp_id_r (Comma.smap f)), <- comp_id_l.
    2: rewrite <- (comp_id_r (Comma.tmap f)), <- comp_id_l.
    all: symmetry.
    all: revert Hf.
    all: change (?a -> ?b) with (impl a b).
    all: f_equiv.
    1, 3: red.
    all: f_equal.
    1, 2: symmetry.
    all: apply is_eq_refl.
    1, 2: destruct Hy.
    3, 4: destruct Hx.
    all: apply is_eq_id.
  }
  destruct H.
  subst θs θt.
  apply fun_eq, proj1 in inv_l.
  apply fun_eq, proj1 in inv_r.
  simpl in inv_l, inv_r.
  clear φ_id φ_comp θ_id θ_comp.
  simpl in Hφf, Hθf.
  constructor.
  1: unshelve eexists.
  2: unshelve eexists.
  1: exists (fun p => φ' (fst p) (snd p)).
  2: exists (fun p => θ' (fst p) (snd p)).
  3, 4: natural_eq p.
  1, 2: unfold comp; simpl; unfold tcomp.
  1, 2: intros [x1 y1] [x2 y2] [f1 f2].
  1, 2: simpl in f1, f2 |- *.
  1, 2: extensionality g.
  1, 2: change (x2 ~> x1) in f1.
  + assert (Hf: f2 ∘ g = f2 ∘ g ∘ fmap F (id x1)).
      rewrite fmap_id.
      symmetry.
      apply comp_id_r.
    set (p1 := Comma.Obj F (id D) x1 y1 g).
    set (p2 := (Comma.Obj F (id D) x1 y2 (f2 ∘ g))).
    set (f := Comma.Hom F (id D) p1 p2 (id x1) f2 Hf).
    specialize (Hφf p1 p2 f) as H.
    simpl in H.
    rewrite H, comp_id_r.
    clear p1 p2 f Hf H.
    specialize (inv_r (Comma.Obj (id C) G x2 y2 (φ' x1 y2 (f2 ∘ g) ∘ f1))) as H.
    simpl in H.
    apply Comma.obj_eq, proj2, proj2 in H.
    specialize (H eq_refl eq_refl).
    simpl in H.
    rewrite !fmap_id, comp_id_l, comp_id_r in H.
    rewrite <- H; clear H.
    f_equal.
    specialize (inv_l (Comma.Obj F (id D) x1 y2 (f2 ∘ g))) as H.
    simpl in H.
    apply Comma.obj_eq, proj2, proj2 in H.
    specialize (H eq_refl eq_refl).
    simpl in H.
    rewrite !fmap_id, comp_id_l, comp_id_r in H.
    rewrite <- H at 1; clear H.
    set (g' := φ' x1 y2 (f2 ∘ g)).
    symmetry.
    assert (Hf: fmap G (id y2) ∘ (g' ∘ f1) = g' ∘ f1).
      rewrite fmap_id.
      apply comp_id_l.
    set (p1 := Comma.Obj (id C) G x2 y2 (g' ∘ f1)).
    set (p2 := Comma.Obj (id C) G x1 y2 g').
    set (f := Comma.Hom (id C) G p1 p2 f1 (id y2) Hf).
    specialize (Hθf p1 p2 f) as H.
    simpl in H.
    rewrite comp_id_l in H.
    exact H.
  + rewrite <- !comp_assoc.
    assert (Hf: fmap G (id y1) ∘ (g ∘ f1) = g ∘ f1).
      rewrite fmap_id.
      apply comp_id_l.
    set (p1 := (Comma.Obj (id C) G x2 y1 (g ∘ f1))).
    set (p2 := Comma.Obj (id C) G x1 y1 g).
    set (f := Comma.Hom (id C) G p1 p2 f1 (id y1) Hf).
    specialize (Hθf p1 p2 f) as H.
    simpl in H.
    rewrite <- H, comp_id_l.
    clear p1 p2 f Hf H.
    specialize (inv_l (Comma.Obj F (id D) x2 y2 (f2 ∘ θ' x2 y1 (g ∘ f1)))) as H.
    simpl in H.
    apply Comma.obj_eq, proj2, proj2 in H.
    specialize (H eq_refl eq_refl).
    simpl in H.
    rewrite !fmap_id, comp_id_l, comp_id_r in H.
    rewrite <- H; clear H.
    f_equal.
    specialize (inv_r (Comma.Obj (id C) G x2 y1 (g ∘ f1))) as H.
    simpl in H.
    apply Comma.obj_eq, proj2, proj2 in H.
    specialize (H eq_refl eq_refl).
    simpl in H.
    rewrite !fmap_id, comp_id_l, comp_id_r in H.
    rewrite <- H at 1; clear H.
    set (g' := θ' x2 y1 (g ∘ f1)).
    assert (Hf: f2 ∘ g' = f2 ∘ g' ∘ fmap F (id x2)).
      rewrite fmap_id.
      symmetry.
      apply comp_id_r.
    set (p1 := Comma.Obj F (id D) x2 y1 g').
    set (p2 := Comma.Obj F (id D) x2 y2 (f2 ∘ g')).
    set (f := Comma.Hom F (id D) p1 p2 (id x2) f2 Hf).
    specialize (Hφf p1 p2 f) as H.
    simpl in H.
    rewrite comp_id_r in H.
    exact H.
  + destruct p as [x y].
    simpl.
    extensionality f.
    unfold comp, id; simpl.
    unfold tcomp, tid.
    specialize (inv_l (Comma.Obj F (id D) x y f)) as H.
    simpl in H.
    apply Comma.obj_eq, proj2, proj2 in H.
    specialize (H eq_refl eq_refl).
    simpl in H.
    rewrite fmap_id, comp_id_l, comp_id_r in H.
    exact H.
  + destruct p as [x y].
    simpl.
    extensionality f.
    unfold comp, id; simpl.
    unfold tcomp, tid.
    specialize (inv_r (Comma.Obj (id C) G x y f)) as H.
    simpl in H.
    apply Comma.obj_eq, proj2, proj2 in H.
    specialize (H eq_refl eq_refl).
    simpl in H.
    rewrite fmap_id, comp_id_l, comp_id_r in H.
    exact H.
Qed.

Lemma Adjoint_Comma: F -| G <-> exists φ: F ↓ id D <~> id C ↓ G, Comma2Prod (id C) G ∘ φ = Comma2Prod F (id D).
Proof.
  split.
  exact adjoint2comma.
  intros [φ Hφ].
  exact (comma2adjoint φ Hφ).
Qed.
