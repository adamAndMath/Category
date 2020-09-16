Require Export Structure.

Section ProdCategory.
Context (C D: Category).

Definition Prod_mixin: Category.mixin_of (C * D) :=
  Category.Mixin (C * D) (fun p q => (fst p ~> fst q) * (snd p ~> snd q))%type
  (fun p => (id (fst p), id (snd p)))
  (fun _ _ _ f g => (fst f ∘ fst g, snd f ∘ snd g))
  (fun _ _ _ _ f g h => f_equal2 pair (comp_assoc _ _ _) (comp_assoc _ _ _))
  (fun _ _ f => eq_trans (f_equal2 pair (comp_id_l (fst f)) (comp_id_l (snd f))) (eq_sym (surjective_pairing f)))
  (fun _ _ f => eq_trans (f_equal2 pair (comp_id_r (fst f)) (comp_id_r (snd f))) (eq_sym (surjective_pairing f))).

End ProdCategory.

Canonical Prod (C D: Category): Category :=
  Category.Pack (C * D) (Prod_mixin C D).

Definition Fork {C D E: Category} (F: C ~> D) (G: C ~> E): C ~> Prod D E := {|
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

Lemma Fork_FstSnd {C D E: Category} (F: C ~> D) (G: C ~> E) (H: C ~> Prod D E): H = Fork F G <-> Fst ∘ H = F /\ Snd ∘ H = G.
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

Definition CatProd_Top_mixin (C D: TopCategory): TopCategory.mixin_of (C × D) :=
  TopCategory.Mixin _ (1, 1) (fun p => (to_one, to_one))
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
