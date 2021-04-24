Require Export Structure.

Module Prod.

Section category.
Context (C D: Category).

Definition cat_mixin: Category.mixin_of (C * D) :=
  Category.Mixin (C * D) (fun p q => (fst p ~> fst q) * (snd p ~> snd q))%type
  (fun p => (id (fst p), id (snd p)))
  (fun _ _ _ f g => (fst f ∘ fst g, snd f ∘ snd g))
  (fun _ _ _ _ f g h => f_equal2 pair (comp_assoc _ _ _) (comp_assoc _ _ _))
  (fun _ _ f => eq_trans (f_equal2 pair (comp_id_l (fst f)) (comp_id_l (snd f))) (eq_sym (surjective_pairing f)))
  (fun _ _ f => eq_trans (f_equal2 pair (comp_id_r (fst f)) (comp_id_r (snd f))) (eq_sym (surjective_pairing f))).

Canonical cat: Category :=
  Category.Pack (C * D) cat_mixin.

Lemma obj_eq (p q: cat): p = q <-> fst p = fst q /\ snd p = snd q.
Proof.
  split.
  intros.
  now subst q.
  destruct p as [x y], q as [x' y'].
  simpl.
  intros [Hx Hy].
  now subst x' y'.
Qed.

Lemma hom_eq {p q: cat} (f g: p ~> q): f = g <-> fst f = fst g /\ snd f = snd g.
Proof.
  split.
  intros.
  now subst g.
  destruct f as [f f'], g as [g g'].
  simpl.
  intros [H H'].
  now subst g g'.
Qed.

End category.

End Prod.

Canonical Prod.cat.
Notation Prod := Prod.cat.

Section CatProd.

Definition Fork {C D E: Category} (F: Functor C D) (G: Functor C E): Functor C (Prod D E) := {|
  fobj x := (F x, G x);
  fmap _ _ f := (fmap F f, fmap G f);
  fmap_id x := f_equal2 pair fmap_id fmap_id;
  fmap_comp _ _ _ f g := f_equal2 pair (fmap_comp f g) (fmap_comp f g);
|}.

Definition Fst {C D: Category}: Prod C D ~> C := {|
  fobj := fst;
  fmap _ _ := fst;
  fmap_id x := eq_refl;
  fmap_comp _ _ _ f g := eq_refl;
|}.

Definition Snd {C D: Category}: Prod C D ~> D := {|
  fobj := snd;
  fmap _ _ := snd;
  fmap_id x := eq_refl;
  fmap_comp _ _ _ f g := eq_refl;
|}.

Lemma Fork_FstSnd {C D E: Category} (F: Functor C D) (G: Functor C E) (H: Functor C (Prod D E)): H = Fork F G <-> Fst ∘ H = F /\ Snd ∘ H = G.
Proof.
  split.
  + intros ?.
    subst H.
    split.
    1, 2: now fun_eq x y f.
  + intros [? ?].
    subst F G.
    rename H into F.
    symmetry.
    fun_eq x y f.
    symmetry.
    apply surjective_pairing.
    rewrite <- (surjective_pairing (fmap F f)).
    revert H H0.
    generalize (F x) (F y) (fmap F f).
    clear.
    intros [x1 x2] [y1 y2] f ex ey.
    rewrite !eq_iso_refl.
    unfold inv; simpl.
    rewrite comp_id_r.
    apply comp_id_l.
Qed.

Definition CatProd_mixin: ProdCategory.mixin_of Cat :=
  ProdCategory.Mixin Cat Prod (@Fork) (@Fst) (@Snd) (@Fork_FstSnd).

Canonical CatProd: ProdCategory :=
  ProdCategory.Pack Cat CatProd_mixin.
End CatProd.

Definition CatProd_Top_mixin (C D: TopCategory): TopCategory.mixin_of (C × D) :=
  TopCategory.Mixin _ (1, 1) (fun p => (!, !))
  (fun _ f => eq_trans (f_equal2 pair (to_one_unique _) (to_one_unique _)) (eq_sym (surjective_pairing f))).

Canonical CatProd_Top (C D: TopCategory): TopCategory :=
  TopCategory.Pack (C × D) (CatProd_Top_mixin C D).

Lemma Prod_fork_pi {C D: ProdCategory} (x y z: C * D) (f: x ~> y) (g: x ~> z) (h: x ~> (fst y × fst z, snd y × snd z)): h = (⟨fst f, fst g⟩, ⟨snd f, snd g⟩) <-> ((π₁, π₁): (fst y × fst z, snd y × snd z) ~> y) ∘ h = f /\ ((π₂, π₂): (fst y × fst z, snd y × snd z) ~> z) ∘ h = g.
Proof.
  split.
  + intros H.
    subst h.
    split.
    all: unfold comp; simpl.
    rewrite (surjective_pairing f) at 3.
    f_equal.
    1, 2: apply pi1_fork.
    rewrite (surjective_pairing g) at 3.
    f_equal.
    1, 2: apply pi2_fork.
  + intros [Hf Hg].
    subst f g.
    rewrite (surjective_pairing h) at 1.
    symmetry.
    f_equal.
    all: apply fork_eta.
Qed.

Definition CatProd_Prod_mixin (C D: ProdCategory): ProdCategory.mixin_of (C × D) :=
  ProdCategory.Mixin _ (fun x y => (fst x × fst y, snd x × snd y))
  (fun _ _ _ f g => (⟨fst f, fst g⟩, ⟨snd f, snd g⟩))
  (fun _ _ => (π₁, π₁))
  (fun _ _ => (π₂, π₂))
  Prod_fork_pi.

Canonical CatProd_Prod (C D: ProdCategory): ProdCategory :=
  ProdCategory.Pack (C × D) (CatProd_Prod_mixin C D).

Definition bf {S1 S2 T: Category} (F: Bifunctor S1 S2 T): Functor (Prod S1 S2) T := {|
  fobj p := F (fst p) (snd p);
  fmap p q f := bmap F (fst f) (snd f);
  fmap_id p := bmap_id F (fst p) (snd p);
  fmap_comp p1 p2 p3 f g := bmap_comp F (fst f) (fst g) (snd f) (snd g);
|}.

Definition fb {S1 S2 T: Category} (F: Functor (Prod S1 S2) T): Bifunctor S1 S2 T := {|
  bobj x y := F (x, y);
  bmap x1 x2 y1 y2 f g := @fmap _ _ F (x1, y1) (x2, y2) (f, g);
  bmap_id x y := @fmap_id _ _ F (x, y);
  bmap_comp x1 x2 x3 y1 y2 y3 f1 f2 g1 g2 := @fmap_comp _ _ F (x1, y1) (x2, y2) (x3, y3) (f1, g1) (f2, g2);
|}.

Lemma fb_bf {S1 S2 T: Category} (F: Bifunctor S1 S2 T): fb (bf F) = F.
Proof.
  apply bifun_eq.
  split.
  + intros x y.
    reflexivity.
  + intros x1 x2 y1 y2 f g e1 e2.
    rewrite !eq_iso_refl; clear e1 e2.
    simpl.
    rewrite comp_id_r.
    apply comp_id_l.
Qed.

Lemma bf_fb {S1 S2 T: Category} (F: Functor (Prod S1 S2) T): bf (fb F) = F.
Proof.
  apply fun_eq.
  split.
  + intros [x y].
    reflexivity.
  + intros [x1 y1] [x2 y2] [f g] e1 e2.
    rewrite !eq_iso_refl; clear e1 e2.
    simpl.
    rewrite comp_id_r.
    apply comp_id_l.
Qed.

Section CoProd.
Context (C D: Category).

Definition CoProd_to: co (C × D) ~> (co C) × (co D) := {|
  fobj (p: co (C × D)) := p: ((co C) × (co D));
  fmap _ _ f := f;
  fmap_id _ := eq_refl;
  fmap_comp _ _ _ _ _ := eq_refl;
|}.

Definition CoProd_from: (co C) × (co D) ~> co (C × D) := {|
  fobj (p: ((co C) × (co D))) := p: co (C × D);
  fmap _ _ f := f;
  fmap_id _ := eq_refl;
  fmap_comp _ _ _ _ _ := eq_refl;
|}.

Lemma CoProd_inv_l: CoProd_from ∘ CoProd_to = id (co (C × D)).
Proof.
  fun_eq p q f.
  change (q ~> p) in f.
  rewrite !eq_iso_refl.
  simpl.
  change (@comp (co ?C) _ _ _ ?f ?g) with (@comp C _ _ _ g f).
  change (@id (co ?C) ?x) with (@id C x).
  rewrite comp_id_l.
  apply (comp_id_r f).
Qed.

Lemma CoProd_inv_r: CoProd_to ∘ CoProd_from = id (co C × co D).
Proof.
  fun_eq p q f.
  change (q ~> p) in f.
  rewrite !eq_iso_refl.
  simpl.
  change (@comp (co ?C × co ?D) _ _ _ ?f ?g) with (@comp (C × D) _ _ _ g f).
  change (@id (co ?C × co ?D) ?x) with (@id (C × D) x).
  rewrite comp_id_l.
  apply (comp_id_r f).
Qed.

Definition CoProd: co (C × D) <~> (co C) × (co D) :=
  Isomorphism.Pack CoProd_to (Isomorphism.Mixin _ _ _ CoProd_to CoProd_from CoProd_inv_l CoProd_inv_r).

Lemma co_prod: co (C × D) ≃ co C × co D.
Proof.
  constructor.
  exact CoProd.
Qed.
End CoProd.
