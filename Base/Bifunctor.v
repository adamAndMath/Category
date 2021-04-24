Require Export Base.Functor.

Structure Bifunctor (S1 S2 T: Category) := {
  bobj: S1 -> S2 -> T;
  bmap {a1 a2: S1} {b1 b2: S2}: a1 ~> a2 -> b1 ~> b2 -> bobj a1 b1 ~> bobj a2 b2;
  bmap_id (a: S1) (b: S2): bmap (id a) (id b) = id (bobj a b);
  bmap_comp {a1 a2 a3: S1} {b1 b2 b3: S2} (f1: a2 ~> a3) (f2: a1 ~> a2) (g1: b2 ~> b3) (g2: b1 ~> b2): bmap (f1 ∘ f2) (g1 ∘ g2) = bmap f1 g1 ∘ bmap f2 g2;
}.

Arguments bobj {S1 S2 T} _ _ _.
Arguments bmap {S1 S2 T} _ {a1 a2 b1 b2} _ _.
Arguments bmap_id {S1 S2 T} _ _ _.
Arguments bmap_comp {S1 S2 T} _ {a1 a2 a3 b1 b2 b3} f1 f2 g1 g2.

Coercion bobj: Bifunctor >-> Funclass.

Theorem bifun_eq {S1 S2 T: Category} (F G: Bifunctor S1 S2 T): F = G <-> (forall x y, F x y = G x y) /\ (forall x1 x2 y1 y2 (f: x1 ~> x2) (g: y1 ~> y2) (e1: F x1 y1 = G x1 y1) (e2: F x2 y2 = G x2 y2), eq_iso e2 ∘ bmap F f g = bmap G f g ∘ eq_iso e1).
Proof.
  split.
  + intros H.
    subst G.
    split.
    intros x y.
    reflexivity.
    intros x1 x2 y1 y2 f g e1 e2.
    rewrite !eq_iso_refl.
    simpl.
    rewrite comp_id_r.
    apply comp_id_l.
  + destruct F as [Fobj Fmap Fmap_id Fmap_comp], G as [Gobj Gmap Gmap_id Gmap_comp]; simpl.
    intros [Hobj Hmap].
    enough (Fobj = Gobj).
    subst Gobj; clear Hobj.
    enough (Fmap = Gmap).
    subst Gmap; clear Hmap.
    f_equal; apply proof_irrelevance.
    - extensionality x1.
      extensionality x2.
      extensionality y1.
      extensionality y2.
      extensionality f.
      extensionality g.
      specialize (Hmap x1 x2 y1 y2 f g eq_refl eq_refl).
      simpl in Hmap.
      rewrite comp_id_l, comp_id_r in Hmap.
      exact Hmap.
    - extensionality x.
      extensionality y.
      apply Hobj.
Qed.

Structure Trifunctor (S1 S2 S3 T: Category) := {
  tobj: S1 -> S2 -> S3 -> T;
  tmap {a1 a2: S1} {b1 b2: S2} {c1 c2: S3}: a1 ~> a2 -> b1 ~> b2 -> c1 ~> c2 -> tobj a1 b1 c1 ~> tobj a2 b2 c2;
  tmap_id (a: S1) (b: S2) (c: S3): tmap (id a) (id b) (id c) = id (tobj a b c);
  tmap_comp {a1 a2 a3: S1} {b1 b2 b3: S2} {c1 c2 c3: S3} (f1: a2 ~> a3) (f2: a1 ~> a2) (g1: b2 ~> b3) (g2: b1 ~> b2) (h1: c2 ~> c3) (h2: c1 ~> c2): tmap (f1 ∘ f2) (g1 ∘ g2) (h1 ∘ h2) = tmap f1 g1 h1 ∘ tmap f2 g2 h2;
}.

Arguments tobj {S1 S2 S3 T} _ _ _ _.
Arguments tmap {S1 S2 S3 T} _ {a1 a2 b1 b2 c1 c2} _ _ _.
Arguments tmap_id {S1 S2 S3 T} _ _ _ _.
Arguments tmap_comp {S1 S2 S3 T} _ {a1 a2 a3 b1 b2 b3 c1 c2 c3} f1 f2 g1 g2 h1 h2.

Coercion tobj: Trifunctor >-> Funclass.

Theorem trifun_eq {S1 S2 S3 T: Category} (F G: Trifunctor S1 S2 S3 T): F = G <-> (forall x y z, F x y z = G x y z) /\ (forall x1 x2 y1 y2 z1 z2 (f: x1 ~> x2) (g: y1 ~> y2) (h: z1 ~> z2) (e1: F x1 y1 z1 = G x1 y1 z1) (e2: F x2 y2 z2 = G x2 y2 z2), eq_iso e2 ∘ tmap F f g h = tmap G f g h ∘ eq_iso e1).
Proof.
  split.
  + intros H.
    subst G.
    split.
    intros x y z.
    reflexivity.
    intros x1 x2 y1 y2 z1 z2 f g h e1 e2.
    rewrite !eq_iso_refl.
    simpl.
    rewrite comp_id_r.
    apply comp_id_l.
  + destruct F as [Fobj Fmap Fmap_id Fmap_comp], G as [Gobj Gmap Gmap_id Gmap_comp]; simpl.
    intros [Hobj Hmap].
    enough (Fobj = Gobj).
    subst Gobj; clear Hobj.
    enough (Fmap = Gmap).
    subst Gmap; clear Hmap.
    f_equal; apply proof_irrelevance.
    - extensionality x1.
      extensionality x2.
      extensionality y1.
      extensionality y2.
      extensionality z1.
      extensionality z2.
      extensionality f.
      extensionality g.
      extensionality h.
      specialize (Hmap x1 x2 y1 y2 z1 z2 f g h eq_refl eq_refl).
      simpl in Hmap.
      rewrite comp_id_l, comp_id_r in Hmap.
      exact Hmap.
    - extensionality x.
      extensionality y.
      extensionality z.
      apply Hobj.
Qed.

Program Definition fix_l {S1 S2 T: Category} (F: Bifunctor S1 S2 T) (x: S1): Functor S2 T := {|
  fobj y := F x y;
  fmap y1 y2 f := bmap F (id x) f;
|}.
Next Obligation.
  apply bmap_id.
Qed.
Next Obligation.
  rewrite <- (comp_id_l (id x)) at 1.
  apply bmap_comp.
Qed.

Program Definition fix_r {S1 S2 T: Category} (F: Bifunctor S1 S2 T) (y: S2): Functor S1 T := {|
  fobj x := F x y;
  fmap x1 x2 f := bmap F f (id y);
|}.
Next Obligation.
  apply bmap_id.
Qed.
Next Obligation.
  rewrite <- (comp_id_l (id y)) at 1.
  apply bmap_comp.
Qed.

Program Definition bfix_l {S1 S2 S3 T: Category} (F: Trifunctor S1 S2 S3 T) (x: S1): Bifunctor S2 S3 T := {|
  bobj y z := F x y z;
  bmap y1 y2 z1 z2 f g := tmap F (id x) f g;
|}.
Next Obligation.
  apply tmap_id.
Qed.
Next Obligation.
  rewrite <- (comp_id_l (id x)) at 1.
  apply tmap_comp.
Qed.

Program Definition bfix_m {S1 S2 S3 T: Category} (F: Trifunctor S1 S2 S3 T) (y: S2): Bifunctor S1 S3 T := {|
  bobj x z := F x y z;
  bmap x1 x2 z1 z2 f g := tmap F f (id y) g;
|}.
Next Obligation.
  apply tmap_id.
Qed.
Next Obligation.
  rewrite <- (comp_id_l (id y)) at 1.
  apply tmap_comp.
Qed.

Program Definition bfix_r {S1 S2 S3 T: Category} (F: Trifunctor S1 S2 S3 T) (z: S3): Bifunctor S1 S2 T := {|
  bobj x y := F x y z;
  bmap x1 x2 y1 y2 f g := tmap F f g (id z);
|}.
Next Obligation.
  apply tmap_id.
Qed.
Next Obligation.
  rewrite <- (comp_id_l (id z)) at 1.
  apply tmap_comp.
Qed.

Definition const_l {C D: Category} (S: Category) (F: Functor C D): Bifunctor S C D := {|
  bobj _ y := F y;
  bmap _ _ y1 y2 _ f := fmap F f;
  bmap_id _ y := fmap_id;
  bmap_comp _ _ _ y1 y2 y3 _ _ f g := fmap_comp f g;
|}.

Definition const_r {C D: Category} (S: Category) (F: Functor C D): Bifunctor C S D := {|
  bobj x _ := F x;
  bmap x1 x2 _ _ f _ := fmap F f;
  bmap_id x _ := fmap_id;
  bmap_comp x1 x2 x3 _ _ _ f g _ _ := fmap_comp f g;
|}.

Definition bconst_l {S1 S2 T: Category} (C: Category) (F: Bifunctor S1 S2 T): Trifunctor C S1 S2 T := {|
  tobj _ x y := F x y;
  tmap _ _ x1 x2 y1 y2 _ f g := bmap F f g;
  tmap_id _ x y := bmap_id F x y;
  tmap_comp _ _ _ x1 x2 x3 y1 y2 y3 _ _ f1 f2 g1 g2 := bmap_comp F f1 f2 g1 g2;
|}.

Definition bconst_m {S1 S2 T: Category} (C: Category) (F: Bifunctor S1 S2 T): Trifunctor S1 C S2 T := {|
  tobj x _ y := F x y;
  tmap x1 x2 _ _ y1 y2 f _ g := bmap F f g;
  tmap_id x _ y := bmap_id F x y;
  tmap_comp x1 x2 x3 _ _ _ y1 y2 y3 f1 f2 _ _ g1 g2 := bmap_comp F f1 f2 g1 g2;
|}.

Definition bconst_r {S1 S2 T: Category} (C: Category) (F: Bifunctor S1 S2 T): Trifunctor S1 S2 C T := {|
  tobj x y _ := F x y;
  tmap x1 x2 y1 y2 _ _ f g _ := bmap F f g;
  tmap_id x y _ := bmap_id F x y;
  tmap_comp x1 x2 x3 y1 y2 y3 _ _ _ f1 f2 g1 g2 _ _ := bmap_comp F f1 f2 g1 g2;
|}.

Section bmap_iso.
Context {S1 S2 T: Category} {x1 x2: S1} {y1 y2: S2} (F: Bifunctor S1 S2 T) (i1: x1 <~> x2) (i2: y1 <~> y2).

Program Definition ibmap_mixin: Isomorphism.mixin_of (bmap F i1 i2) :=
  Isomorphism.Mixin _ _ _ (bmap F i1 i2) (bmap F i1⁻¹ i2⁻¹)
  (eq_trans (eq_sym (bmap_comp F _ _ _ _)) (eq_trans (f_equal2 _ (inv_l _) (inv_l _)) (bmap_id F _ _)))
  (eq_trans (eq_sym (bmap_comp F _ _ _ _)) (eq_trans (f_equal2 _ (inv_r _) (inv_r _)) (bmap_id F _ _))).

Global Canonical ibmap: F x1 y1 <~> F x2 y2 :=
  Isomorphism.Pack (bmap F i1 i2) ibmap_mixin.

End bmap_iso.

Section tmap_iso.
Context {S1 S2 S3 T: Category} {x1 x2: S1} {y1 y2: S2} {z1 z2: S3} (F: Trifunctor S1 S2 S3 T) (i1: x1 <~> x2) (i2: y1 <~> y2) (i3: z1 <~> z2).

Program Definition itmap_mixin: Isomorphism.mixin_of (tmap F i1 i2 i3) :=
  Isomorphism.Mixin _ _ _ (tmap F i1 i2 i3) (tmap F i1⁻¹ i2⁻¹ i3⁻¹)
  (eq_trans (eq_sym (tmap_comp F _ _ _ _ _ _)) (eq_trans (f_equal3 _ (inv_l _) (inv_l _) (inv_l _)) (tmap_id F _ _ _)))
  (eq_trans (eq_sym (tmap_comp F _ _ _ _ _ _)) (eq_trans (f_equal3 _ (inv_r _) (inv_r _) (inv_r _)) (tmap_id F _ _ _))).

Global Canonical itmap: F x1 y1 z1 <~> F x2 y2 z2 :=
  Isomorphism.Pack (tmap F i1 i2 i3) itmap_mixin.

End tmap_iso.

Lemma bmap_is_iso {S1 S2 T: Category} {x1 x2: S1} {y1 y2: S2} (F: Bifunctor S1 S2 T) (f: x1 ~> x2) (g: y1 ~> y2): is_iso f -> is_iso g -> is_iso (bmap F f g).
Proof.
  intros [f' [Hfl Hfr]] [g' [Hgl Hgr]].
  exists (bmap F f' g'); split.
  all: rewrite <- bmap_comp, <- bmap_id.
  all: now f_equal.
Qed.

Lemma tmap_is_iso {S1 S2 S3 T: Category} {x1 x2: S1} {y1 y2: S2} {z1 z2: S3} (F: Trifunctor S1 S2 S3 T) (f: x1 ~> x2) (g: y1 ~> y2) (h: z1 ~> z2): is_iso f -> is_iso g -> is_iso h -> is_iso (tmap F f g h).
Proof.
  intros [f' [Hfl Hfr]] [g' [Hgl Hgr]] [h' [Hhl Hhr]].
  exists (tmap F f' g' h'); split.
  all: rewrite <- tmap_comp, <- tmap_id.
  all: now f_equal.
Qed.

Lemma bmap_is_eq {S1 S2 T: Category} {x1 x2: S1} {y1 y2: S2} (F: Bifunctor S1 S2 T) (f: x1 ~> x2) (g: y1 ~> y2): is_eq f -> is_eq g -> is_eq (bmap F f g).
Proof.
  intros [ex Hx] [ey Hy].
  subst f g x2 y2.
  simpl.
  rewrite bmap_id.
  apply is_eq_id.
Qed.

Lemma tmap_is_eq {S1 S2 S3 T: Category} {x1 x2: S1} {y1 y2: S2} {z1 z2: S3} (F: Trifunctor S1 S2 S3 T) (f: x1 ~> x2) (g: y1 ~> y2) (h: z1 ~> z2): is_eq f -> is_eq g -> is_eq h -> is_eq (tmap F f g h).
Proof.
  intros [ex Hx] [ey Hy] [ez Hz].
  subst f g h x2 y2 z2.
  simpl.
  rewrite tmap_id.
  apply is_eq_id.
Qed.

Theorem bmap_inv {S1 S2 T: Category} {x1 x2: S1} {y1 y2: S2} (F: Bifunctor S1 S2 T) (i: x1 <~> x2) (j: y1 <~> y2): bmap F i⁻¹ j⁻¹ = (ibmap F i j)⁻¹.
Proof. reflexivity. Qed.

Theorem tmap_inv {S1 S2 S3 T: Category} {x1 x2: S1} {y1 y2: S2} {z1 z2: S3} (F: Trifunctor S1 S2 S3 T) (i: x1 <~> x2) (j: y1 <~> y2) (k: z1 <~> z2): tmap F i⁻¹ j⁻¹ k⁻¹ = (itmap F i j k)⁻¹.
Proof. reflexivity. Qed.

Theorem ibmap_inv {S1 S2 T: Category} {x1 x2: S1} {y1 y2: S2} (F: Bifunctor S1 S2 T) (i: x1 <~> x2) (j: y1 <~> y2): ibmap F i⁻¹ j⁻¹ = (ibmap F i j)⁻¹.
Proof. now apply iso_eq. Qed.

Theorem itmap_inv {S1 S2 S3 T: Category} {x1 x2: S1} {y1 y2: S2} {z1 z2: S3} (F: Trifunctor S1 S2 S3 T) (i: x1 <~> x2) (j: y1 <~> y2) (k: z1 <~> z2): itmap F i⁻¹ j⁻¹ k⁻¹ = (itmap F i j k)⁻¹.
Proof. now apply iso_eq. Qed.
