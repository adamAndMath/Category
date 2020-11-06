Require Export Base.Natural.

Definition is_equiv {C D: Category} (F: C ~> D) :=
  exists G: D ~> C, G ∘ F ≃ id C /\ F ∘ G ≃ id D.

Instance is_equiv_iso (C D: Category): Proper (isomorphic (Fun C D) ==> iff) is_equiv.
Proof.
  enough (Proper (isomorphic (Fun C D) ==> impl) is_equiv).
  now split; apply H.
  intros F G FG [F' H].
  exists F'.
  now rewrite <- FG.
Qed.

Definition cequiv (C D: Category) :=
  exists F: C ~> D, is_equiv F.

Infix "≈" := cequiv (at level 70, no associativity).

Instance cequivalence: Equivalence cequiv.
Proof.
  split.
  + intros C.
    exists (id C), (id C).
    split.
    all: now rewrite comp_id_l.
  + intros C D [F [G [Hc Hd]]].
    now exists G, F.
  + intros A B C [F [F' [HF HF']]] [G [G' [HG HG']]].
    exists (G ∘ F), (F' ∘ G').
    split.
    all: rewrite comp_assoc.
    1: rewrite <- (comp_assoc F').
    2: rewrite <- (comp_assoc G).
    1: rewrite HG.
    2: rewrite HF'.
    all: now rewrite comp_id_r.
Qed.

Instance iso_cequiv: subrelation (isomorphic Cat) cequiv.
Proof.
  intros C D [I].
  exists (to I), (to I⁻¹).
  split.
  now rewrite inv_l.
  now rewrite inv_r.
Qed.

Lemma is_equiv_esurj {C D: Category} (F: C ~> D): is_equiv F -> esurj F.
Proof.
  intros [G [[η] [ϵ]]] y.
  exists (G y).
  change ((F ∘ G) y ≃ (id D) y).
  now apply fobj_iso.
Qed.

Lemma is_equiv_faithful {C D: Category} (F: C ~> D): is_equiv F -> faithful F.
Proof.
  intros [G [[η] [ϵ]]] x y f g H.
  apply (f_equal (fun f => to η y ∘ fmap G f)) in H.
  setoid_rewrite (naturality (to η)) in H.
  simpl in H.
  apply is_iso_epic in H.
  exact H.
  apply (is_iso_transform η).
  apply iso_is_iso.
Qed.

Lemma is_equiv_full {C D: Category} (F: C ~> D): is_equiv F -> full F.
Proof.
  intros [G [[η] [ϵ]]] x y g.
  set (f := to η y ∘ fmap G g ∘ to η⁻¹ x).
  simpl in f.
  exists f.
  assert (faithful G) as HG.
  apply is_equiv_faithful.
  now exists F.
  apply HG.
  apply (is_iso_monic (to η y)).
  apply is_iso_transform, iso_is_iso.
  setoid_rewrite (naturality (to η)).
  simpl.
  unfold f.
  rewrite <- comp_assoc.
  change (from η x ∘ to η x) with ((η⁻¹ ∘ η) x).
  rewrite inv_l.
  apply comp_id_r.
Qed.

Lemma is_equiv_fully_faithful {C D: Category} (F: C ~> D): is_equiv F -> fully_faithful F.
Proof.
  intros HF.
  apply full_and_faithful.
  split.
  apply is_equiv_full, HF.
  apply is_equiv_faithful, HF.
Qed.

Lemma is_equiv_alt_units {C D: Category} (F: C ~> D): fully_faithful F -> esurj F -> exists (G: D ~> C) (ɛ: F ∘ G <~> id D) (η: G ∘ F <~> id C), (forall x, to ɛ (F x) = fmap F (to η x)) /\ (forall x, to η (G x) = fmap G (to ɛ x)).
Proof.
  intros fu es.
  apply full_and_faithful in fu.
  destruct fu as [fu fa].
  apply ex_forall in es.
  destruct es as [gobj Hr].
  assert (forall x, gobj (F x) ≃ x) as Hl.
    intros x.
    apply (fully_faithful_iso F).
    now apply full_and_faithful.
    apply Hr.
  apply inhabit_forall in Hr.
  destruct Hr as [ɛ].
  assert (forall a b f, exists f', fmap F f' = (ɛ b)⁻¹ ∘ f ∘ ɛ a).
    intros a b f.
    apply fu.
  generalize (fun a b => ex_forall _ (H a b)).
  clear H; intros H.
  generalize (fun a => ex_forall _ (H a)).
  clear H; intros H.
  apply ex_forall in H.
  destruct H as [gmap gmap_spec].
  assert (exists G: D ~> C, fobj G = gobj /\ forall e: gobj = fobj G, @fmap _ _ G = match e in _ = x return (forall a b, a ~> b -> x a ~> x b) with eq_refl => gmap end).
    unshelve eexists.
    exists gobj gmap.
    3: simpl.
    1: intros a.
    2: intros a b c f g.
    1, 2: apply fa.
    rewrite fmap_id, gmap_spec.
    rewrite comp_id_r.
    apply inv_l.
    rewrite fmap_comp, !gmap_spec.
    rewrite <- (comp_id_r f ) at 1.
    rewrite <- (inv_r (ɛ b)).
    rewrite (comp_assoc f), <- (comp_assoc (f ∘ ɛ b)).
    rewrite comp_assoc, <- comp_assoc.
    f_equal.
    apply comp_assoc.
    split.
    reflexivity.
    intros e.
    assert (e = eq_refl) by apply proof_irrelevance.
    subst e.
    reflexivity.
  destruct H as [G [Ho Hm]].
  subst gobj.
  specialize (Hm eq_refl).
  simpl in Hm.
  subst gmap.
  exists G.
  rename ɛ into ɛ'.
  assert (exists ɛ: F ∘ G <~> id D, transform_iso ɛ = ɛ').
    unshelve eexists.
    2: extensionality x.
    2: apply iso_eq.
    1: unshelve eexists.
    2: unshelve eexists.
    5: simpl.
    1: exists (fun x => to (ɛ' x)).
    2: exists (fun x => to (ɛ' x)⁻¹).
    3, 4: natural_eq x.
    5: reflexivity.
    1, 2: intros x y f.
    1, 2: simpl fmap.
    1, 2: rewrite gmap_spec.
    2: symmetry.
    1, 2: rewrite <- comp_assoc.
    rewrite comp_assoc.
    1, 2: rewrite inv_r.
    apply comp_id_l.
    apply comp_id_r.
    apply inv_l.
    apply inv_r.
  destruct H as [ɛ].
  subst ɛ'.
  simpl in gmap_spec.
  unfold from in gmap_spec; simpl in gmap_spec.
  change (from ?i) with (to i⁻¹) in gmap_spec.
  exists ɛ.
  assert (forall x, exists i, to ɛ (F x) = fmap F (to i)).
    intros x.
    assert (exists y, G y ≃ x).
      now exists (F x).
    destruct H as [y [i]].
    exists (i · imap G (transform_iso ɛ y · imap F i⁻¹)).
    simpl.
    change (from i) with (to i⁻¹).
    rewrite fmap_comp.
    rewrite gmap_spec.
    rewrite (comp_assoc (to ɛ⁻¹ y)).
    change (to ɛ⁻¹ y ∘ to ɛ y) with ((ɛ⁻¹ ∘ ɛ) y).
    rewrite inv_l.
    simpl transform.
    rewrite comp_id_l.
    rewrite comp_assoc.
    rewrite <- fmap_comp.
    rewrite inv_r, fmap_id.
    symmetry.
    apply comp_id_l.
  apply ex_forall in H.
  destruct H as [η Hη].
  unshelve eexists.
  1: unshelve eexists.
  2: unshelve eexists.
  1: exists (fun x => to (η x)).
  2: exists (fun x => to (η x)⁻¹).
  3, 4: natural_eq x.
  5: simpl.
  1, 2: intros x y f.
  1, 2: simpl.
  2: symmetry.
  all: change (from ?i) with (to i⁻¹).
  1, 2: apply fa.
  1, 2: rewrite !fmap_comp.
  1, 2: rewrite gmap_spec.
  rewrite <- !Hη.
  rewrite <- comp_assoc, comp_assoc.
  change (to ɛ ?y ∘ to ɛ⁻¹ ?y) with ((ɛ ∘ ɛ⁻¹) y).
  rewrite inv_r.
  apply comp_id_l.
  apply (is_iso_monic (to ɛ (F y))).
  apply is_iso_transform, iso_is_iso.
  rewrite <- 2 comp_assoc, comp_assoc.
  change (to ɛ ?y ∘ to ɛ⁻¹ ?y) with ((ɛ ∘ ɛ⁻¹) y).
  rewrite inv_r.
  simpl transform.
  rewrite comp_id_l.
  rewrite !Hη.
  rewrite (comp_assoc (fmap F (η y))).
  rewrite <- !fmap_comp.
  f_equal.
  rewrite !inv_r.
  rewrite comp_id_l.
  apply comp_id_r.
  apply inv_l.
  apply inv_r.
  split.
  apply Hη.
  intros y.
  apply fa.
  rewrite <- Hη, gmap_spec.
  symmetry.
  change (to ɛ⁻¹ y ∘ to ɛ y) with ((ɛ⁻¹ ∘ ɛ) y).
  rewrite inv_l.
  apply comp_id_l.
Qed.

Lemma is_equiv_alt {C D: Category} (F: C ~> D): is_equiv F <-> fully_faithful F /\ esurj F.
Proof.
  split.
  intros H.
  split.
  now apply is_equiv_fully_faithful.
  now apply is_equiv_esurj.
  intros [fu es].
  destruct (is_equiv_alt_units F fu es) as [G [ɛ [η _]]].
  now exists G.
Qed.

Lemma is_equiv_units {C D: Category} (F: C ~> D): is_equiv F -> exists (G: D ~> C) (ɛ: F ∘ G <~> id D) (η: G ∘ F <~> id C), (forall x, to ɛ (F x) = fmap F (to η x)) /\ (forall x, to η (G x) = fmap G (to ɛ x)).
Proof.
  intros HF.
  apply is_equiv_alt in HF.
  now apply is_equiv_alt_units.
Qed.

Structure iso2 (C D: Category) := {
  to2: C ~> D;
  from2: D ~> C;
  iunit: from2 ∘ to2 <~> id C;
  icounit: to2 ∘ from2 <~> id D;
  iunit_to x: fmap to2 (to iunit x) = to icounit (to2 x);
  iunit_from x: fmap from2 (to icounit x) = to iunit (from2 x);
}.

Arguments to2 {C D} _.
Arguments from2 {C D} _.
Arguments iunit {C D} _.
Arguments icounit {C D} _.
Arguments iunit_to {C D} _ _.
Arguments iunit_from {C D} _ _.

Infix "<=>" := iso2 (at level 70, no associativity).

Coercion to2: iso2 >-> hom.

Definition cto_fun {C D} (F: C <=> D): Functor C D := to2 F.
Coercion cto_fun: iso2 >-> Functor.

Definition cto_fobj {C D} (F: C <=> D): C -> D := F.
Coercion cto_fobj: iso2 >-> Funclass.

Definition cinv {C D: Category} (F: C <=> D): D <=> C := {|
  to2 := from2 F;
  from2 := to2 F;
  iunit := icounit F;
  icounit := iunit F;
  iunit_to := iunit_from F;
  iunit_from := iunit_to F;
|}.

Notation "F ⁻" := (cinv F) (at level 9).

Lemma inv2_l {C D: Category} (F: C <=> D): F⁻ ∘ F ≃ id C.
Proof.
  constructor.
  exact (iunit F).
Qed.

Lemma inv2_r {C D: Category} (F: C <=> D): F ∘ F⁻ ≃ id D.
Proof.
  constructor.
  exact (icounit F).
Qed.

Lemma iso2_eq (C D: Category) (F G: C <=> D): F = G <-> to2 F = G /\ to2 F⁻ = G⁻ /\ (forall (e: F⁻ ∘ F = G⁻ ∘ G), to (iunit F) = iunit G ∘ eq_iso e).
Proof.
  split.
  + intros H.
    subst G.
    repeat split.
    intros e.
    rewrite eq_iso_refl; clear e.
    symmetry.
    apply comp_id_r.
  + destruct F as [F F' Fη Fɛ Fto Ffrom], G as [G G' Gη Gɛ Gto Gfrom].
    simpl.
  intros [H1 [H2 H]].
  subst G G'.
  specialize (H eq_refl).
  simpl in H.
  rewrite comp_id_r in H.
  apply iso_eq in H.
  subst Gη.
  enough (Fɛ = Gɛ).
  subst Gɛ.
  f_equal; apply proof_irrelevance.
  apply iso_eq.
  natural_eq y.
  apply (is_equiv_faithful F').
  now exists F.
  setoid_rewrite Gfrom.
  apply Ffrom.
Qed.

Lemma cinv_invol {C D: Category} (F: C <=> D): F⁻⁻ = F.
Proof.
  now destruct F.
Qed.

Lemma cinv_iso {C D: Category} (F G: C <=> D): to2 F ≃ G <-> to2 F⁻ ≃ G⁻.
Proof.
  revert C D F G.
  enough (forall C D (F G: C <=> D), to2 F ≃ G -> to2 F⁻ ≃ G⁻).
  all: intros C D F G.
  split.
  rewrite <- (cinv_invol F) at 1.
  rewrite <- (cinv_invol G) at 1.
  1, 2: apply H.
  intros H.
  rewrite <- (comp_id_r F⁻).
  rewrite <- (inv2_r G).
  rewrite comp_assoc.
  rewrite <- H.
  rewrite inv2_l.
  rewrite comp_id_l.
  reflexivity.
Qed.

Lemma iunit_co {C D: Category} (F: C <=> D) (x: C): fmap F (to (iunit F) x) = to (iunit F⁻) (F x).
Proof. apply iunit_to. Qed.

Lemma iunit_co' {C D: Category} (F: C <=> D) (x: D): fmap F⁻ (to (iunit F⁻) x) = to (iunit F) (F⁻ x).
Proof. apply iunit_from. Qed.

Program Definition iso_iso2 (C D: Category) (i: C <~> D): C <=> D := {|
  to2 := i;
  from2 := i⁻¹;
  iunit := eq_iso (inv_l i);
  icounit := eq_iso (inv_r i);
|}.
Next Obligation.
  apply is_eq_unique.
  apply fmap_is_eq.
  apply (transform_is_eq (eq_iso (inv_l i))).
  apply eq_iso_is_eq.
  apply (transform_is_eq (eq_iso (inv_r i))).
  apply eq_iso_is_eq.
Qed.
Next Obligation.
  apply is_eq_unique.
  apply fmap_is_eq.
  apply (transform_is_eq (eq_iso (inv_r i))).
  apply eq_iso_is_eq.
  apply (transform_is_eq (eq_iso (inv_l i))).
  apply eq_iso_is_eq.
Qed.

Definition iso2_id (C: Category): C <=> C := {|
  to2 := id C;
  from2 := id C;
  iunit := λ (id C);
  icounit := λ (id C);
  iunit_to _ := eq_refl;
  iunit_from _ := eq_refl;
|}.

Program Definition iso2_comp {A B C: Category} (F: B <=> C) (G: A <=> B): A <=> C := {|
  to2 := F ∘ G;
  from2 := G⁻ ∘ F⁻;
  iunit := iunit G · (G⁻ <|| (λ G · (iunit F ||> G) · α F⁻ F G)) · (α G⁻ F⁻ (F ∘ G))⁻¹;
  icounit := iunit F⁻ · (F <|| (λ F⁻ · (iunit G⁻ ||> F⁻) · α G G⁻ F⁻)) · (α F G (G⁻ ∘ F⁻))⁻¹;
|}.
Next Obligation.
  rewrite !comp_id_l, !comp_id_r.
  change (from2 ?F) with (to2 F⁻).
  rewrite fmap_comp.
  setoid_rewrite (iunit_co G x).
  setoid_rewrite (@naturality _ _ _ _ (to (icounit G))).
  simpl fmap at 2.
  rewrite fmap_comp.
  f_equal.
  apply iunit_co.
Qed.
Next Obligation.
  rewrite !comp_id_l, !comp_id_r.
  change (from2 ?F) with (to2 F⁻).
  rewrite fmap_comp.
  setoid_rewrite (iunit_co' F x).
  setoid_rewrite (@naturality _ _ _ _ (to (iunit F))).
  simpl fmap at 2.
  rewrite fmap_comp.
  f_equal.
  apply iunit_co.
Qed.

Instance co_equiv: Proper (cequiv ==> cequiv) co.
Proof.
  intros C D [F [G [Hl Hr]]].
  exists (fmap Co' F), (fmap Co' G).
  split.
  all: rewrite <- (@fmap_comp _ _ Co').
  all: rewrite <- (@fmap_id _ _ Co').
  all: simpl.
  all: change (cof ?F) with (to (CoFun _ _) F).
  all: apply fobj_iso.
  1, 3: reflexivity.
  all: rewrite iso_co.
  all: assumption.
Qed.

Lemma iso2_is_equiv {C D: Category} (F: C <=> D): is_equiv F.
Proof.
  exists (to2 F⁻).
  split.
  apply inv2_l.
  apply inv2_r.
Qed.

Lemma iso2_cequiv {C D: Category} (F: C <=> D): C ≈ D.
Proof.
  exists (to2 F).
  apply iso2_is_equiv.
Qed.

Lemma is_equiv_ex {C D: Category} (F: C ~> D): is_equiv F -> exists I: C <=> D, to2 I = F.
Proof.
  intros H.
  apply is_equiv_units in H.
  destruct H as [G [ɛ [η [Hto Hfrom]]]].
  unshelve eexists.
  exists F G η ɛ.
  3: reflexivity.
  all: intros x.
  all: symmetry.
  apply Hto.
  apply Hfrom.
Qed.

Definition cequiv_ex (C D: Category): C ≈ D <-> inhabited (C <=> D).
Proof.
  split.
  intros [F H].
  apply is_equiv_ex in H.
  now destruct H.
  intros [F].
  apply iso2_cequiv, F.
Qed.

Lemma iso2_esurj {C D: Category} (F: C <=> D): esurj F.
Proof. apply is_equiv_esurj, iso2_is_equiv. Qed.

Lemma iso2_faithful {C D: Category} (F: C <=> D): faithful F.
Proof. apply is_equiv_faithful, iso2_is_equiv. Qed.

Lemma iso2_full {C D: Category} (F: C <=> D): full F.
Proof. apply is_equiv_full, iso2_is_equiv. Qed.

Lemma iso2_fully_faithful {C D: Category} (F: C <=> D): fully_faithful F.
Proof. apply is_equiv_fully_faithful, iso2_is_equiv. Qed.
