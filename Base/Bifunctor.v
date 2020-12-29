Require Export Functor.

Structure Bifunctor (S1 S2 T: Category) := {
  bobj: S1 -> S2 -> T;
  bmap {a1 a2: S1} {b1 b2: S2} (f: a1 ~> a2) (g: b1 ~> b2): bobj a1 b1 ~> bobj a2 b2;
  bmap_id {a: S1} {b: S2}: bmap (id a) (id b) = id (bobj a b);
  bmap_comp {a1 a2 a3: S1} {b1 b2 b3: S2} (f1: a2 ~> a3) (f2: a1 ~> a2) (g1: b2 ~> b3) (g2: b1 ~> b2): bmap (f1 ∘ f2) (g1 ∘ g2) = bmap f1 g1 ∘ bmap f2 g2;
}.

Arguments bobj {S1 S2 T} _ _ _.
Arguments bmap {S1 S2 T} _ {a1 a2 b1 b2} _ _.
Arguments bmap_id {S1 S2 T} _ {a _}.
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

Section bmap_iso.
Context {S1 S2 T: Category} {x1 x2: S1} {y1 y2: S2} (F: Bifunctor S1 S2 T) (i1: x1 <~> x2) (i2: y1 <~> y2).

Program Definition iimap_mixin: Isomorphism.mixin_of (bmap F i1 i2) :=
  Isomorphism.Mixin _ _ _ (bmap F i1 i2) (bmap F i1⁻¹ i2⁻¹)
  (eq_trans (eq_sym (bmap_comp F _ _ _ _)) (eq_trans (f_equal2 _ (inv_l _) (inv_l _)) (bmap_id F)))
  (eq_trans (eq_sym (bmap_comp F _ _ _ _)) (eq_trans (f_equal2 _ (inv_r _) (inv_r _)) (bmap_id F))).

Global Canonical iimap: F x1 y1 <~> F x2 y2 :=
  Isomorphism.Pack (bmap F i1 i2) iimap_mixin.

End bmap_iso.

Lemma bmap_is_iso {S1 S2 T: Category} {x1 x2: S1} {y1 y2: S2} (F: Bifunctor S1 S2 T) (f: x1 ~> x2) (g: y1 ~> y2): is_iso f -> is_iso g -> is_iso (bmap F f g).
Proof.
  intros [f' [Hfl Hfr]] [g' [Hgl Hgr]].
  exists (bmap F f' g'); split.
  all: rewrite <- bmap_comp, <- bmap_id.
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

Theorem bmap_inv {S1 S2 T: Category} {x1 x2: S1} {y1 y2: S2} (F: Bifunctor S1 S2 T) (i: x1 <~> x2) (j: y1 <~> y2): bmap F i⁻¹ j⁻¹ = (iimap F i j)⁻¹.
Proof. reflexivity. Qed.

Theorem iimap_inv {S1 S2 T: Category} {x1 x2: S1} {y1 y2: S2} (F: Bifunctor S1 S2 T) (i: x1 <~> x2) (j: y1 <~> y2): iimap F i⁻¹ j⁻¹ = (iimap F i j)⁻¹.
Proof. now apply iso_eq. Qed.
