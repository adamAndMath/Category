Require Export Structure.

Definition ZERO_mixin: Category.mixin_of Empty_set :=
  Category.Mixin Empty_set (Empty_set_rect _)
  (Empty_set_rect _) (Empty_set_rect _)
  (Empty_set_rect _)
  (Empty_set_rect _)
  (Empty_set_rect _).

Canonical ZERO: Category :=
  Category.Pack Empty_set ZERO_mixin.

Definition from_ZERO {C: Category}: ZERO ~> C := {|
  fobj := Empty_set_rect _;
  fmap := Empty_set_rect _;
  fmap_id := Empty_set_rect _;
  fmap_comp := Empty_set_rect _;
|}.

Lemma from_ZERO_unique (C: Category) (F: ZERO ~> C): from_ZERO = F.
Proof.
  fun_eq x y f.
  all: destruct x.
Qed.

Definition CatBot_mixin: BotCategory.mixin_of Cat :=
  BotCategory.Mixin Cat ZERO (@from_ZERO) from_ZERO_unique.

Canonical CatBot: BotCategory :=
  BotCategory.Pack Cat CatBot_mixin.

Definition ZERO_Prod_mixin: ProdCategory.mixin_of 0 :=
  ProdCategory.Mixin 0 (Empty_set_rect _)
  (Empty_set_rect _) (Empty_set_rect _) (Empty_set_rect _)
  (Empty_set_rect _).

Canonical ZERO_Prod: ProdCategory :=
  ProdCategory.Pack 0 ZERO_Prod_mixin.

Definition ZERO_Coprod_mixin: CoprodCategory.mixin_of 0 :=
  CoprodCategory.Mixin 0 (Empty_set_rect _)
  (Empty_set_rect _) (Empty_set_rect _) (Empty_set_rect _)
  (Empty_set_rect _).

Canonical ZERO_Coprod: CoprodCategory :=
  CoprodCategory.Pack 0 ZERO_Coprod_mixin.

Definition coZero2Zero: co 0 ~> 0 := {|
  fobj := Empty_set_rect _: co 0 -> (0: Category);
  fmap := Empty_set_rect _;
  fmap_id := Empty_set_ind _;
  fmap_comp := Empty_set_ind _;
|}.

Lemma toZero_inv_l {C: Category} (F: C ~> 0): from_zero ∘ F = id C.
Proof.
  fun_eq x y f.
  destruct (F x).
  set (F x).
  unfold o.
  destruct o.
Qed.

Lemma toZero_inv_r {C: Category} (F: C ~> 0): F ∘ from_zero = id 0.
Proof.
  fun_eq x y f.
  all: destruct x.
Qed.

Definition toZero_iso_mixin {C: Category} (F: C ~> 0): Isomorphism.mixin_of F :=
  Isomorphism.Mixin _ _ _ F from_zero (toZero_inv_l F) (toZero_inv_r F).

Canonical toZero_iso {C: Category} (F: C ~> 0): C <~> 0 :=
  Isomorphism.Pack F (toZero_iso_mixin F).

Lemma iso_0 (C: Category): C ≃ 0 <-> inhabited (C ~> 0).
Proof.
  split.
  + intros [I].
    constructor.
    exact I.
  + intros [F].
    constructor.
    apply toZero_iso, F.
Qed.
