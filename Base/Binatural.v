Require Export Base.Bifunctor.
Require Export Base.Natural.

Structure Binatural {S1 S2 T: Category} (F G: Bifunctor S1 S2 T) := {
  bitransform (x: S1) (y: S2): F x y ~> G x y;
  binaturality {x1 x2: S1} {y1 y2: S2} (f: x1 ~> x2) (g: y1 ~> y2): bitransform x2 y2 ∘ bmap F f g = bmap G f g ∘ bitransform x1 y1;
}.

Arguments bitransform {_ _ _ _ _} _ _ _.
Arguments binaturality {_ _ _ _ _} _ {_ _ _ _} _ _.

Coercion bitransform: Binatural >-> Funclass.

Theorem binatural_eq {S1 S2 T: Category} {F G: Bifunctor S1 S2 T} (η ϵ: Binatural F G): η = ϵ <-> (forall x y, η x y = ϵ x y).
Proof.
  split.
  now intros [].
  destruct η as [η Hη], ϵ as [ϵ Hϵ]; simpl.
  intros H.
  enough (η = ϵ); [subst ϵ|].
  f_equal; apply proof_irrelevance.
  extensionality x.
  extensionality y.
  apply H.
Qed.

Structure Trinatural {S1 S2 S3 T: Category} (F G: Trifunctor S1 S2 S3 T) := {
  tritransform (x: S1) (y: S2) (z: S3): F x y z ~> G x y z;
  trinaturality {x1 x2: S1} {y1 y2: S2} {z1 z2: S3} (f: x1 ~> x2) (g: y1 ~> y2) (h: z1 ~> z2): tritransform x2 y2 z2 ∘ tmap F f g h = tmap G f g h ∘ tritransform x1 y1 z1;
}.

Arguments tritransform {_ _ _ _ _ _} _ _ _ _.
Arguments trinaturality {_ _ _ _ _ _} _ {_ _ _ _ _ _} _ _ _.

Coercion tritransform: Trinatural >-> Funclass.

Theorem trinatural_eq {S1 S2 S3 T: Category} {F G: Trifunctor S1 S2 S3 T} (η ϵ: Trinatural F G): η = ϵ <-> (forall x y z, η x y z = ϵ x y z).
Proof.
  split.
  now intros [].
  destruct η as [η Hη], ϵ as [ϵ Hϵ]; simpl.
  intros H.
  enough (η = ϵ); [subst ϵ|].
  f_equal; apply proof_irrelevance.
  extensionality x.
  extensionality y.
  extensionality z.
  apply H.
Qed.

Section Bifun.
Context {S1 S2 T: Category}.

Definition binat_id (F: Bifunctor S1 S2 T): Binatural F F := {|
  bitransform x y := id (F x y);
  binaturality x1 x2 y1 y2 f g := eq_trans (comp_id_l _) (eq_sym (comp_id_r _));
|}.

Program Definition binat_comp {F G H: Bifunctor S1 S2 T} (η: Binatural G H) (ϵ: Binatural F G): Binatural F H := {|
  bitransform x y := η x y ∘ ϵ x y;
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite binaturality.
  rewrite !comp_assoc.
  f_equal.
  apply binaturality.
Qed.

Lemma binat_comp_assoc (F G H I: Bifunctor S1 S2 T) (η: Binatural H I) (μ: Binatural G H) (ϵ: Binatural F G): binat_comp η (binat_comp μ ϵ) = binat_comp (binat_comp η μ) ϵ.
Proof.
  apply binatural_eq; simpl.
  intros x y.
  apply comp_assoc.
Qed.

Lemma binat_comp_id_l (F G: Bifunctor S1 S2 T) (η: Binatural F G): binat_comp (binat_id G) η = η.
Proof.
  apply binatural_eq; simpl.
  intros x y.
  apply comp_id_l.
Qed.

Lemma binat_comp_id_r (F G: Bifunctor S1 S2 T) (η: Binatural F G): binat_comp η (binat_id F) = η.
Proof.
  apply binatural_eq; simpl.
  intros x y.
  apply comp_id_r.
Qed.

End Bifun.

Definition Bifun_mixin (S1 S2 T: Category): Category.mixin_of (Bifunctor S1 S2 T) :=
  Category.Mixin (Bifunctor S1 S2 T) Binatural binat_id (@binat_comp S1 S2 T) binat_comp_assoc binat_comp_id_l binat_comp_id_r.

Canonical Bifun (S1 S2 T: Category): Category :=
  Category.Pack (Bifunctor S1 S2 T) (Bifun_mixin S1 S2 T).

Section Trifun.
Context {S1 S2 S3 T: Category}.

Definition trinat_id (F: Trifunctor S1 S2 S3 T): Trinatural F F := {|
  tritransform x y z := id (F x y z);
  trinaturality x1 x2 y1 y2 z1 z2 f g h := eq_trans (comp_id_l _) (eq_sym (comp_id_r _));
|}.

Program Definition trinat_comp {F G H: Trifunctor S1 S2 S3 T} (η: Trinatural G H) (ϵ: Trinatural F G): Trinatural F H := {|
  tritransform x y z := η x y z ∘ ϵ x y z;
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite trinaturality.
  rewrite !comp_assoc.
  f_equal.
  apply trinaturality.
Qed.

Lemma trinat_comp_assoc (F G H I: Trifunctor S1 S2 S3 T) (η: Trinatural H I) (μ: Trinatural G H) (ϵ: Trinatural F G): trinat_comp η (trinat_comp μ ϵ) = trinat_comp (trinat_comp η μ) ϵ.
Proof.
  apply trinatural_eq; simpl.
  intros x y z.
  apply comp_assoc.
Qed.

Lemma trinat_comp_id_l (F G: Trifunctor S1 S2 S3 T) (η: Trinatural F G): trinat_comp (trinat_id G) η = η.
Proof.
  apply trinatural_eq; simpl.
  intros x y z.
  apply comp_id_l.
Qed.

Lemma trinat_comp_id_r (F G: Trifunctor S1 S2 S3 T) (η: Trinatural F G): trinat_comp η (trinat_id F) = η.
Proof.
  apply trinatural_eq; simpl.
  intros x y z.
  apply comp_id_r.
Qed.

End Trifun.

Definition Trifun_mixin (S1 S2 S3 T: Category): Category.mixin_of (Trifunctor S1 S2 S3 T) :=
  Category.Mixin (Trifunctor S1 S2 S3 T) Trinatural trinat_id (@trinat_comp S1 S2 S3 T) trinat_comp_assoc trinat_comp_id_l trinat_comp_id_r.

Canonical Trifun (S1 S2 S3 T: Category): Category :=
  Category.Pack (Trifunctor S1 S2 S3 T) (Trifun_mixin S1 S2 S3 T).

Definition bitransform_iso_mixin {S1 S2 T: Category} {F G: Bifunctor S1 S2 T} (I: F <~> G) (x: S1) (y: S2): Isomorphism.mixin_of (to I x y) :=
  Isomorphism.Mixin _ _ _ (to I x y) (to I⁻¹ x y) ((f_equal (fun f => bitransform f x y) (inv_l I))) ((f_equal (fun f => bitransform f x y) (inv_r I))).

Canonical bitransform_iso {S1 S2 T: Category} {F G: Bifunctor S1 S2 T} (I: F <~> G) (x: S1) (y: S2): F x y <~> G x y :=
  Isomorphism.Pack _ (bitransform_iso_mixin I x y).

Definition tritransform_iso_mixin {S1 S2 S3 T: Category} {F G: Trifunctor S1 S2 S3 T} (I: F <~> G) (x: S1) (y: S2) (z: S3): Isomorphism.mixin_of (to I x y z) :=
  Isomorphism.Mixin _ _ _ (to I x y z) (to I⁻¹ x y z) ((f_equal (fun f => tritransform f x y z) (inv_l I))) ((f_equal (fun f => tritransform f x y z) (inv_r I))).

Canonical tritransform_iso {S1 S2 S3 T: Category} {F G: Trifunctor S1 S2 S3 T} (I: F <~> G) (x: S1) (y: S2) (z: S3): F x y z <~> G x y z :=
  Isomorphism.Pack _ (tritransform_iso_mixin I x y z).

Instance bobj_iso (S1 S2 T: Category): Proper (isomorphic _ ==> isomorphic S1 ==> isomorphic S2 ==> isomorphic T) bobj.
Proof.
  intros F G [I] x1 x2 [i] y1 y2 [j].
  transitivity (F x2 y2).
  constructor.
  exact (ibmap F i j).
  constructor.
  exact (bitransform_iso I x2 y2).
Qed.

Instance tobj_iso (S1 S2 S3 T: Category): Proper (isomorphic _ ==> isomorphic S1 ==> isomorphic S2 ==> isomorphic S3 ==> isomorphic T) tobj.
Proof.
  intros F G [I] x1 x2 [i] y1 y2 [j] z1 z2 [k].
  transitivity (F x2 y2 z2).
  constructor.
  exact (itmap F i j k).
  constructor.
  exact (tritransform_iso I x2 y2 z2).
Qed.

Lemma is_iso_bitransform {S1 S2 T: Category} {F G: Bifunctor S1 S2 T} (η: F ~> G): is_iso η <-> forall x y, is_iso (η x y).
Proof.
  split.
  + intros [ϵ [Hl Hr]] x y.
    exists (ϵ x y); split.
    apply (proj1 (binatural_eq _ _) Hl).
    apply (proj1 (binatural_eq _ _) Hr).
  + intros H.
    generalize (fun x => proj1 (ex_forall _) (H x)).
    clear H; intros H.
    apply ex_forall in H.
    destruct H as [ɛ H].
    unshelve eexists.
    exists ɛ.
    2: split; apply binatural_eq, H.
    intros x1 x2 y1 y2 f g.
    rewrite <- (comp_id_r (bmap G f g)).
    rewrite <- (proj2 (H x1 y1)).
    rewrite (comp_assoc (bmap G f g)).
    rewrite <- binaturality.
    rewrite <- comp_assoc, comp_assoc.
    rewrite (proj1 (H x2 y2)).
    apply comp_id_l.
Qed.

Lemma bitransform_is_eq {S1 S2 T: Category} {F G: Bifunctor S1 S2 T} (η: F ~> G) (x: S1) (y: S2): is_eq η -> is_eq (η x y).
Proof.
  intros [e H].
  subst η G.
  apply is_eq_id.
Qed.

Lemma is_iso_tritransform {S1 S2 S3 T: Category} {F G: Trifunctor S1 S2 S3 T} (η: F ~> G): is_iso η <-> forall x y z, is_iso (η x y z).
Proof.
  split.
  + intros [ϵ [Hl Hr]] x y z.
    exists (ϵ x y z); split.
    apply (proj1 (trinatural_eq _ _) Hl).
    apply (proj1 (trinatural_eq _ _) Hr).
  + intros H.
    generalize (fun x y => proj1 (ex_forall _) (H x y)).
    clear H; intros H.
    generalize (fun x => proj1 (ex_forall _) (H x)).
    clear H; intros H.
    apply ex_forall in H.
    destruct H as [ɛ H].
    unshelve eexists.
    exists ɛ.
    2: split; apply trinatural_eq, H.
    intros x1 x2 y1 y2 z1 z2 f g h.
    rewrite <- (comp_id_r (tmap G f g h)).
    rewrite <- (proj2 (H x1 y1 z1)).
    rewrite (comp_assoc (tmap G f g h)).
    rewrite <- trinaturality.
    rewrite <- comp_assoc, comp_assoc.
    rewrite (proj1 (H x2 y2 z2)).
    apply comp_id_l.
Qed.

Lemma tritransform_is_eq {S1 S2 S3 T: Category} {F G: Trifunctor S1 S2 S3 T} (η: F ~> G) (x: S1) (y: S2) (z: S3): is_eq η -> is_eq (η x y z).
Proof.
  intros [e H].
  subst η G.
  apply is_eq_id.
Qed.

Theorem bifun_iso {S1 S2 T: Category} (F G: Bifunctor S1 S2 T): F ≃ G <-> exists I: forall x y, F x y <~> G x y, forall x1 x2 y1 y2 (f: x1 ~> x2) (g: y1 ~> y2), I x2 y2 ∘ bmap F f g = bmap G f g ∘ I x1 y1.
Proof.
  split.
  + intros [I].
    exists (bitransform_iso I).
    intros x y f.
    unfold transform_iso, inv; simpl.
    apply binaturality.
  + intros [I H].
    constructor.
    unshelve eexists.
    unshelve econstructor.
    exact I.
    2: unshelve eexists.
    2: unshelve econstructor.
    2: exact (fun x y => (I x y)⁻¹).
    3, 4: apply binatural_eq; simpl.
    3, 4: intros x y.
    3: apply inv_l.
    3: apply inv_r.
    all: intros x1 x2 y1 y2 f g; simpl.
    apply H.
    rewrite <- (comp_id_r _), <- (inv_r (I x1 y1)).
    rewrite comp_assoc.
    f_equal.
    rewrite <- comp_id_l, <- (inv_l (I x2 y2)).
    rewrite <- !comp_assoc.
    f_equal.
    symmetry.
    apply H.
Qed.

Theorem trifun_iso {S1 S2 S3 T: Category} (F G: Trifunctor S1 S2 S3 T): F ≃ G <-> exists I: forall x y z, F x y z <~> G x y z, forall x1 x2 y1 y2 z1 z2 (f: x1 ~> x2) (g: y1 ~> y2) (h: z1 ~> z2), I x2 y2 z2 ∘ tmap F f g h = tmap G f g h ∘ I x1 y1 z1.
Proof.
  split.
  + intros [I].
    exists (tritransform_iso I).
    intros x y z f.
    unfold transform_iso, inv; simpl.
    apply trinaturality.
  + intros [I H].
    constructor.
    unshelve eexists.
    unshelve econstructor.
    exact I.
    2: unshelve eexists.
    2: unshelve econstructor.
    2: exact (fun x y z => (I x y z)⁻¹).
    3, 4: apply trinatural_eq; simpl.
    3, 4: intros x y z.
    3: apply inv_l.
    3: apply inv_r.
    all: intros x1 x2 y1 y2 z1 z2 f g h; simpl.
    apply H.
    rewrite <- (comp_id_r _), <- (inv_r (I x1 y1 z1)).
    rewrite comp_assoc.
    f_equal.
    rewrite <- comp_id_l, <- (inv_l (I x2 y2 z2)).
    rewrite <- !comp_assoc.
    f_equal.
    symmetry.
    apply H.
Qed.

Lemma binat_monic {S1 S2 T: Category} {F G: Bifunctor S1 S2 T} (η: F ~> G): (forall x y, monic (η x y)) -> monic η.
Proof.
  intros Hη Z α β H.
  apply binatural_eq; simpl.
  intros x y.
  apply Hη.
  change ((η ∘ α) x y = (η ∘ β) x y).
  now f_equal.
Qed.

Lemma binat_epic {S1 S2 T: Category} {F G: Bifunctor S1 S2 T} (η: F ~> G): (forall x y, epic (η x y)) -> epic η.
Proof.
  intros Hη Z α β H.
  apply binatural_eq; simpl.
  intros x y.
  apply Hη.
  change ((α ∘ η) x y = (β ∘ η) x y).
  now f_equal.
Qed.

Lemma trinat_monic {S1 S2 S3 T: Category} {F G: Trifunctor S1 S2 S3 T} (η: F ~> G): (forall x y z, monic (η x y z)) -> monic η.
Proof.
  intros Hη Z α β H.
  apply trinatural_eq; simpl.
  intros x y z.
  apply Hη.
  change ((η ∘ α) x y z = (η ∘ β) x y z).
  now f_equal.
Qed.

Lemma trinat_epic {S1 S2 S3 T: Category} {F G: Trifunctor S1 S2 S3 T} (η: F ~> G): (forall x y z, epic (η x y z)) -> epic η.
Proof.
  intros Hη Z α β H.
  apply trinatural_eq; simpl.
  intros x y z.
  apply Hη.
  change ((α ∘ η) x y z = (β ∘ η) x y z).
  now f_equal.
Qed.

Lemma binat_splitmonic {S1 S2 T: Category} {F G: Bifunctor S1 S2 T} (η: F ~> G): splitmonic η -> forall x y, splitmonic (η x y).
Proof.
  intros [ϵ H] x y.
  exists (ϵ x y).
  change ((ϵ ∘ η) x y = id F x y).
  now f_equal.
Qed.

Lemma binat_splitepic {S1 S2 T: Category} {F G: Bifunctor S1 S2 T} (η: F ~> G): splitepic η -> forall x y, splitepic (η x y).
Proof.
  intros [ϵ H] x y.
  exists (ϵ x y).
  change ((η ∘ ϵ) x y = id G x y).
  now f_equal.
Qed.

Lemma trinat_splitmonic {S1 S2 S3 T: Category} {F G: Trifunctor S1 S2 S3 T} (η: F ~> G): splitmonic η -> forall x y z, splitmonic (η x y z).
Proof.
  intros [ϵ H] x y z.
  exists (ϵ x y z).
  change ((ϵ ∘ η) x y z = id F x y z).
  now f_equal.
Qed.

Lemma trinat_splitepic {S1 S2 S3 T: Category} {F G: Trifunctor S1 S2 S3 T} (η: F ~> G): splitepic η -> forall x y z, splitepic (η x y z).
Proof.
  intros [ϵ H] x y z.
  exists (ϵ x y z).
  change ((η ∘ ϵ) x y z = id G x y z).
  now f_equal.
Qed.

Lemma binat_is_iso {S1 S2 T: Category} {F G: Bifunctor S1 S2 T} (η: F ~> G): is_iso η <-> forall x y, is_iso (η x y).
Proof.
  split.
  + intros [ϵ H] x y.
    exists (ϵ x y); split.
    1: change ((ϵ ∘ η) x y = id F x y).
    2: change ((η ∘ ϵ) x y = id G x y).
    all: now f_equal.
  + intros H.
    generalize (fun x => proj1 (ex_forall _) (H x)).
    clear H; intros H.
    apply ex_forall in H.
    destruct H as [ϵ H].
    unshelve eexists.
    exists ϵ.
    2: split; apply binatural_eq, H.
    intros x1 x2 y1 y2 f g.
    rewrite <- (comp_id_r (ϵ x2 y2 ∘ bmap G f g)).
    rewrite <- comp_id_r.
    rewrite <- (proj2 (H x1 y1)).
    rewrite !comp_assoc.
    f_equal.
    rewrite <- !comp_assoc.
    rewrite <- binaturality.
    rewrite comp_assoc.
    rewrite !(proj1 (H _ _)).
    rewrite comp_id_r.
    apply comp_id_l.
Qed.

Lemma trinat_is_iso {S1 S2 S3 T: Category} {F G: Trifunctor S1 S2 S3 T} (η: F ~> G): is_iso η <-> forall x y z, is_iso (η x y z).
Proof.
  split.
  + intros [ϵ H] x y z.
    exists (ϵ x y z); split.
    1: change ((ϵ ∘ η) x y z = id F x y z).
    2: change ((η ∘ ϵ) x y z = id G x y z).
    all: now f_equal.
  + intros H.
    generalize (fun x y => proj1 (ex_forall _) (H x y)).
    clear H; intros H.
    generalize (fun x => proj1 (ex_forall _) (H x)).
    clear H; intros H.
    apply ex_forall in H.
    destruct H as [ϵ H].
    unshelve eexists.
    exists ϵ.
    2: split; apply trinatural_eq, H.
    intros x1 x2 y1 y2 z1 z2 f g h.
    rewrite <- (comp_id_r (ϵ x2 y2 z2 ∘ tmap G f g h)).
    rewrite <- comp_id_r.
    rewrite <- (proj2 (H x1 y1 z1)).
    rewrite !comp_assoc.
    f_equal.
    rewrite <- !comp_assoc.
    rewrite <- trinaturality.
    rewrite comp_assoc.
    rewrite !(proj1 (H _ _ _)).
    rewrite comp_id_r.
    apply comp_id_l.
Qed.

Program Definition LComp {X1 X2 Y1 Y2 Z}: Bifunctor (Bifun Y1 Y2 Z) (Bifun X1 X2 Y1) (Trifun X1 X2 Y2 Z) := {|
  bobj F G := {|
    tobj x y z := F (G x y) z;
    tmap x1 x2 y1 y2 z1 z2 f g h := bmap F (bmap G f g) h;
  |};
  bmap F1 F2 G1 G2 η ϵ := {|
    tritransform x y z := bmap F2 (ϵ x y) (id z) ∘ η (G1 x y) z;
  |};
|}.
Next Obligation.
  rewrite bmap_id.
  apply bmap_id.
Qed.
Next Obligation.
  rewrite bmap_comp.
  apply bmap_comp.
Qed.
Next Obligation.
  rewrite <- comp_assoc, binaturality, !comp_assoc.
  f_equal.
  rewrite <- !bmap_comp.
  rewrite comp_id_l, comp_id_r.
  f_equal.
  apply binaturality.
Qed.
Next Obligation.
  rename a into F, b into G.
  apply trinatural_eq; simpl.
  intros x y z.
  rewrite comp_id_r.
  apply bmap_id.
Qed.
Next Obligation.
  rename a1 into F1, a2 into F2, a3 into F3.
  rename b1 into G1, b2 into G2, b3 into G3.
  rename f1 into η1, f2 into η2, g1 into ϵ1, g2 into ϵ2.
  apply trinatural_eq; simpl.
  intros x y z.
  rewrite !comp_assoc.
  f_equal.
  rewrite <- (comp_id_l (id z)) at 1.
  rewrite bmap_comp, <- !comp_assoc.
  f_equal.
  symmetry.
  apply binaturality.
Qed.

Program Definition RComp {X1 X2 Y1 Y2 Z}: Bifunctor (Bifun Y1 Y2 Z) (Bifun X1 X2 Y2) (Trifun Y1 X1 X2 Z) := {|
  bobj F G := {|
    tobj x y z := F x (G y z);
    tmap x1 x2 y1 y2 z1 z2 f g h := bmap F f (bmap G g h);
  |};
  bmap F1 F2 G1 G2 η ϵ := {|
    tritransform x y z := bmap F2 (id x) (ϵ y z) ∘ η x (G1 y z);
  |};
|}.
Next Obligation.
  rewrite bmap_id.
  apply bmap_id.
Qed.
Next Obligation.
  rewrite bmap_comp.
  apply bmap_comp.
Qed.
Next Obligation.
  rewrite <- comp_assoc, binaturality, !comp_assoc.
  f_equal.
  rewrite <- !bmap_comp.
  rewrite comp_id_l, comp_id_r.
  f_equal.
  apply binaturality.
Qed.
Next Obligation.
  rename a into F, b into G.
  apply trinatural_eq; simpl.
  intros x y z.
  rewrite comp_id_r.
  apply bmap_id.
Qed.
Next Obligation.
  rename a1 into F1, a2 into F2, a3 into F3.
  rename b1 into G1, b2 into G2, b3 into G3.
  rename f1 into η1, f2 into η2, g1 into ϵ1, g2 into ϵ2.
  apply trinatural_eq; simpl.
  intros x y z.
  rewrite !comp_assoc.
  f_equal.
  rewrite <- (comp_id_l (id x)) at 1.
  rewrite bmap_comp, <- !comp_assoc.
  f_equal.
  symmetry.
  apply binaturality.
Qed.
