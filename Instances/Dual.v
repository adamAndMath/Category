Require Export Structure.

Section Dual.
Universe U.

Section CoTop.
Context (C: BotCategory: Type@{U}).

Definition CoTop_mixin: TopCategory.mixin_of (co C) :=
  TopCategory.Mixin (co C) 0 (@from_zero C) (@from_zero_unique C).

Canonical CoTop: TopCategory: Type@{U} :=
  TopCategory.Pack (co C) CoTop_mixin.
End CoTop.

Section CoBot.
Context (C: TopCategory: Type@{U}).

Definition CoBot_mixin: BotCategory.mixin_of (co C) :=
  BotCategory.Mixin (co C) 1 (@to_one C) (@to_one_unique C).

Canonical CoBot: BotCategory: Type@{U} :=
  BotCategory.Pack (co C) CoBot_mixin.
End CoBot.

Section CoProd.
Context (C: CoprodCategory: Type@{U}).

Program Definition CoProd_mixin: ProdCategory.mixin_of (co C) :=
  ProdCategory.Mixin (co C) coprod (fun a b c => @merge C b c a) (@in1 C) (@in2 C) (fun a b c f g h => @merge_in C b c a f g h).

Canonical CoProd: ProdCategory: Type@{U} :=
  ProdCategory.Pack (co C) CoProd_mixin.
End CoProd.

Section CoCoprod.
Context (C: ProdCategory: Type@{U}).

Program Definition CoCoprod_mixin: CoprodCategory.mixin_of (co C) :=
  CoprodCategory.Mixin (co C) prod (fun a b c => @fork C c a b) (@π₁ C) (@π₂ C) (fun a b c f g h => @fork_pi C c a b f g h).

Canonical CoCoprod: CoprodCategory: Type@{U} :=
  CoprodCategory.Pack (co C) CoCoprod_mixin.
End CoCoprod.

Section TopCo.
Context (C: Category: Type@{U}) (m: BotCategory.mixin_of (co C): Type@{U}).
Let C' := BotCategory.Pack (co C) m.

Definition TopCo_mixin: TopCategory.mixin_of C :=
  TopCategory.Mixin C (0: C') (@from_zero C') (@from_zero_unique C').

Definition TopCo: TopCategory: Type@{U} :=
  TopCategory.Pack C TopCo_mixin.
End TopCo.

Section BotCo.
Context (C: Category: Type@{U}) (m: TopCategory.mixin_of (co C): Type@{U}).
Let C' := TopCategory.Pack (co C) m.

Definition BotCo_mixin: BotCategory.mixin_of C :=
  BotCategory.Mixin C (1: C') (@to_one C') (@to_one_unique C').

Definition BotCo: BotCategory: Type@{U} :=
  BotCategory.Pack C BotCo_mixin.
End BotCo.

Section ProdCo.
Context (C: Category: Type@{U}) (m: CoprodCategory.mixin_of (co C): Type@{U}).
Let C' := CoprodCategory.Pack (co C) m.

Program Definition ProdCo_mixin: ProdCategory.mixin_of C :=
  ProdCategory.Mixin C (@coprod C') (fun a b c => @merge C' b c a) (@in1 C') (@in2 C') (fun a b c f g h => @merge_in C' b c a f g h).

Definition ProdCo: ProdCategory: Type@{U} :=
  ProdCategory.Pack C ProdCo_mixin.
End ProdCo.

Section CoprodCo.
Context (C: Category: Type@{U}) (m: ProdCategory.mixin_of (co C): Type@{U}).
Let C' := ProdCategory.Pack (co C) m.

Program Definition CoprodCo_mixin: CoprodCategory.mixin_of C :=
  CoprodCategory.Mixin C (@prod C') (fun a b c => @fork C' c a b) (@π₁ C') (@π₂ C') (fun a b c f g h => @fork_pi C' c a b f g h).

Definition CoprodCo: CoprodCategory: Type@{U} :=
  CoprodCategory.Pack C CoprodCo_mixin.
End CoprodCo.

End Dual.
