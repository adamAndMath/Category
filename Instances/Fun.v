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
  rewrite fprod_comp.
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
  rewrite fcoprod_comp.
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
