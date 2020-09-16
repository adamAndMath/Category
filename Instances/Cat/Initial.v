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
