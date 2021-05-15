Require Export Structure.

Section Terminal.
Context (S: Category) (T: TopCategory).

Definition FunOne: Functor S T := {|
  fobj _ := 1;
  fmap _ _ _ := id 1;
  fmap_id _ := eq_refl;
  fmap_comp _ _ _ _ _ := eq_sym (comp_id_l (id 1));
|}.

Program Definition Fun_to_one (F: Functor S T): F ~> FunOne := {|
  transform x := !;
|}.
Next Obligation.
  apply to_one_eq.
Qed.

Lemma Fun_to_one_unique {F: Functor S T} (η: F ~> FunOne): Fun_to_one F = η.
Proof.
  natural_eq x.
  apply to_one_unique.
Qed.

Definition TopFun_mixin: TopCategory.mixin_of (Fun S T) :=
  TopCategory.Mixin (Fun S T) FunOne Fun_to_one (@Fun_to_one_unique).

Canonical TopFun: TopCategory :=
  TopCategory.Pack (Fun S T) TopFun_mixin.

End Terminal.

Section Initial.
Context (S: Category) (T: BotCategory).

Definition FunZero: Functor S T := {|
  fobj _ := 0;
  fmap _ _ _ := id 0;
  fmap_id _ := eq_refl;
  fmap_comp _ _ _ _ _ := eq_sym (comp_id_l (id 0));
|}.

Program Definition Fun_from_zero (F: Functor S T): FunZero ~> F := {|
  transform x := ¡;
|}.
Next Obligation.
  apply from_zero_eq.
Qed.

Lemma Fun_from_zero_unique {F: Functor S T} (η: FunZero ~> F): Fun_from_zero F = η.
Proof.
  natural_eq x.
  apply from_zero_unique.
Qed.

Definition BotFun_mixin: BotCategory.mixin_of (Fun S T) :=
  BotCategory.Mixin (Fun S T) FunZero Fun_from_zero (@Fun_from_zero_unique).

Canonical BotFun: BotCategory :=
  BotCategory.Pack (Fun S T) BotFun_mixin.

End Initial.

Section Product.
Context (S: Category) (T: ProdCategory).

Program Definition FunProd (F G: Functor S T): Functor S T := {|
  fobj x := F x × G x;
  fmap x y f := fmap F f (×) fmap G f;
|}.
Next Obligation.
  rewrite <- fprod_id.
  f_equal.
  all: apply fmap_id.
Qed.
Next Obligation.
  rewrite <- fprod_comp.
  f_equal.
  all: apply fmap_comp.
Qed.

Program Definition Fun_fork {F G H: Functor S T} (η: F ~> G) (ϵ: F ~> H): F ~> FunProd G H := {|
  transform x := ⟨η x, ϵ x⟩;
|}.
Next Obligation.
  rewrite fork_comp, fprod_fork.
  f_equal.
  all: apply naturality.
Qed.

Program Definition Fun_pi1 (F G: Functor S T): FunProd F G ~> F := {|
  transform x := π₁;
|}.
Next Obligation.
  apply pi1_fork.
Qed.

Program Definition Fun_pi2 (F G: Functor S T): FunProd F G ~> G := {|
  transform x := π₂;
|}.
Next Obligation.
  apply pi2_fork.
Qed.

Lemma Fun_fork_pi {F G H: Functor S T} (η: F ~> G) (ϵ: F ~> H) (ρ: F ~> FunProd G H): ρ = Fun_fork η ϵ <-> Fun_pi1 G H ∘ ρ = η /\ Fun_pi2 G H ∘ ρ = ϵ.
Proof.
  split.
  + intros e.
    subst ρ.
    split.
    all: natural_eq x.
    apply pi1_fork.
    apply pi2_fork.
  + intros [e1 e2].
    subst η ϵ.
    natural_eq x.
    symmetry.
    apply fork_eta.
Qed.

Definition ProdFun_mixin: ProdCategory.mixin_of (Fun S T) :=
  ProdCategory.Mixin (Fun S T) FunProd (@Fun_fork) Fun_pi1 Fun_pi2 (@Fun_fork_pi).

Canonical ProdFun: ProdCategory :=
  ProdCategory.Pack (Fun S T) ProdFun_mixin.

End Product.

Section Coproduct.
Context (S: Category) (T: CoprodCategory).

Program Definition FunCoprod (F G: Functor S T): Functor S T := {|
  fobj x := F x + G x;
  fmap x y f := fmap F f (+) fmap G f;
|}.
Next Obligation.
  rewrite <- fcoprod_id.
  f_equal.
  all: apply fmap_id.
Qed.
Next Obligation.
  rewrite <- fcoprod_comp.
  f_equal.
  all: apply fmap_comp.
Qed.

Program Definition Fun_merge {F G H: Functor S T} (η: F ~> H) (ϵ: G ~> H): FunCoprod F G ~> H := {|
  transform x := [η x, ϵ x];
|}.
Next Obligation.
  rewrite merge_comp, merge_fcoprod.
  f_equal.
  all: apply naturality.
Qed.

Program Definition Fun_in1 (F G: Functor S T): F ~> FunCoprod F G := {|
  transform x := in1;
|}.
Next Obligation.
  symmetry.
  apply merge_in1.
Qed.

Program Definition Fun_in2 (F G: Functor S T): G ~> FunCoprod F G := {|
  transform x := in2;
|}.
Next Obligation.
  symmetry.
  apply merge_in2.
Qed.

Lemma Fun_merge_in {F G H: Functor S T} (η: F ~> H) (ϵ: G ~> H) (ρ: FunCoprod F G ~> H): ρ = Fun_merge η ϵ <-> ρ ∘ Fun_in1 F G = η /\ ρ ∘ Fun_in2 F G = ϵ.
Proof.
  split.
  + intros e.
    subst ρ.
    split.
    all: natural_eq x.
    apply merge_in1.
    apply merge_in2.
  + intros [e1 e2].
    subst η ϵ.
    natural_eq x.
    symmetry.
    apply merge_eta.
Qed.

Definition CoprodFun_mixin: CoprodCategory.mixin_of (Fun S T) :=
  CoprodCategory.Mixin (Fun S T) FunCoprod (@Fun_merge) Fun_in1 Fun_in2 (@Fun_merge_in).

Canonical CoprodFun: CoprodCategory :=
  CoprodCategory.Pack (Fun S T) CoprodFun_mixin.

End Coproduct.

Section Cartisian.
Context (S: Category) (T: CartCategory).

Canonical CartFun: CartCategory :=
  CartCategory.Pack (Fun S T) (CartCategory.Class (Fun S T) (TopFun_mixin S T) (ProdFun_mixin S T)).

End Cartisian.

Section SProduct.
Context (S: Category) (T: SProdCategory).

Program Definition SProdFun_mixin := SProdCategory.Mixin (Fun S T)
  (fun I F => {|
    fobj x := ∏ i, F i x;
    fmap x y f := (∏) i, fmap (F i) f;
  |})
  (fun I F G η => {|
    transform x := ∏' i, η i x;
  |})
  (fun I F i => {|
    transform x := @π T I (fun i => F i x) i;
  |})
  _.
Next Obligation.
  setoid_rewrite fmap_id.
  apply spmap_id.
Qed.
Next Obligation.
  setoid_rewrite fmap_comp.
  apply spmap_comp.
Qed.
Next Obligation.
  rewrite spmap_sfork, <- sfork_comp.
  f_equiv.
  intros i.
  apply naturality.
Qed.
Next Obligation.
  apply (pi_spmap (fun i => fmap (F i) f)).
Qed.
Next Obligation.
  setoid_rewrite natural_eq; simpl.
  now setoid_rewrite sfork_ump.
Qed.
Canonical SProdFun := SProdCategory.Pack (Fun S T) SProdFun_mixin.

End SProduct.

Section SCoproduct.
Context (S: Category) (T: SCoprodCategory).

Program Definition SCoprodFun_mixin := SCoprodCategory.Mixin (Fun S T)
  (fun I F => {|
    fobj x := ∑ i, F i x;
    fmap x y f := (∑) i, fmap (F i) f;
  |})
  (fun I F G η => {|
    transform x := ∑' i, η i x;
  |})
  (fun I F i => {|
    transform x := @ι T I (fun i => F i x) i;
  |})
  _.
Next Obligation.
  setoid_rewrite fmap_id.
  apply scpmap_id.
Qed.
Next Obligation.
  setoid_rewrite fmap_comp.
  apply scpmap_comp.
Qed.
Next Obligation.
  rewrite smerge_scpmap, <- comp_smerge.
  f_equiv.
  intros i.
  apply naturality.
Qed.
Next Obligation.
  symmetry.
  apply (scpmap_sinto (fun i => fmap (F i) f)).
Qed.
Next Obligation.
  setoid_rewrite natural_eq; simpl.
  now setoid_rewrite smerge_ump.
Qed.
Canonical SCoprodFun := SCoprodCategory.Pack (Fun S T) SCoprodFun_mixin.

End SCoproduct.

Section Equalizer.
Context (S: Category) (T: EqCategory).

Program Definition FunEqz {F G: Functor S T} (η μ: F ~> G): Functor S T := {|
  fobj X := Eqz (η X) (μ X);
  fmap X Y f := eqz_med (η Y) (μ Y) (fmap F f ∘ eqz (η X) (μ X)) _;
|}.
Next Obligation.
  rewrite !comp_assoc, !naturality, <- !comp_assoc.
  f_equal.
  apply eqz_comm.
Qed.
Next Obligation.
  apply eqz_med_unique.
  rewrite fmap_id, comp_id_l.
  apply comp_id_r.
Qed.
Next Obligation.
  apply eqz_monic.
  rewrite comp_assoc, !eqz_med_comm, <- comp_assoc.
  rewrite eqz_med_comm, comp_assoc.
  f_equal.
  apply fmap_comp.
Qed.

Program Definition Fun_eqz {F G: Functor S T} (η μ: F ~> G): FunEqz η μ ~> F := {|
  transform x := eqz (η x) (μ x);
|}.
Next Obligation.
  apply eqz_med_comm.
Qed.

Lemma Fun_eqz_comm {F G: Functor S T} (η μ: F ~> G): η ∘ Fun_eqz η μ = μ ∘ Fun_eqz η μ.
Proof.
  natural_eq x.
  apply eqz_comm.
Qed.

Program Definition Fun_eqz_med {F G H: Functor S T} (η μ: G ~> H) (e: F ~> G) (He: η ∘ e = μ ∘ e): F ~> FunEqz η μ := {|
  transform x := eqz_med (η x) (μ x) (e x) (f_equal (fun f => transform f x) He);
|}.
Next Obligation.
  apply eqz_monic.
  rewrite !comp_assoc, !eqz_med_comm.
  rewrite <- comp_assoc, eqz_med_comm.
  apply naturality.
Qed.

Lemma Fun_eqz_med_comm {F G H: Functor S T} (η μ: G ~> H) (e: F ~> G) (He: η ∘ e = μ ∘ e): Fun_eqz η μ ∘ (Fun_eqz_med η μ e He) = e.
Proof.
  natural_eq x.
  apply eqz_med_comm.
Qed.

Lemma Fun_eqz_med_unique {F G H: Functor S T} (η μ: G ~> H) (e: F ~> G) (u: F ~> FunEqz η μ) (He: η ∘ e = μ ∘ e): Fun_eqz η μ ∘ u = e -> Fun_eqz_med η μ e He = u.
Proof.
  intros H1.
  subst e.
  natural_eq x.
  now apply eqz_med_unique.
Qed.

Definition EqFun_mixin: EqCategory.mixin_of (Fun S T) :=
  EqCategory.Mixin (Fun S T) (@FunEqz) (@Fun_eqz) (@Fun_eqz_comm) (@Fun_eqz_med) (@Fun_eqz_med_comm) (@Fun_eqz_med_unique).

Canonical EqFun: EqCategory :=
  EqCategory.Pack (Fun S T) EqFun_mixin.

End Equalizer.
