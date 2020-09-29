Require Export Structure.

Section CoTop.
Context (C: BotCategory).

Definition CoTop_mixin: TopCategory.mixin_of (co C) :=
  TopCategory.Mixin (co C) 0 (@from_zero C) (@from_zero_unique C).

Canonical CoTop: TopCategory :=
  TopCategory.Pack (co C) CoTop_mixin.
End CoTop.

Section CoBot.
Context (C: TopCategory).

Definition CoBot_mixin: BotCategory.mixin_of (co C) :=
  BotCategory.Mixin (co C) 1 (@to_one C) (@to_one_unique C).

Canonical CoBot: BotCategory :=
  BotCategory.Pack (co C) CoBot_mixin.
End CoBot.

Section CoProd.
Context (C: CoprodCategory).

Program Definition CoProd_mixin: ProdCategory.mixin_of (co C) :=
  ProdCategory.Mixin (co C) coprod (fun a b c => @merge C b c a) (@in1 C) (@in2 C) (fun a b c f g h => @merge_in C b c a f g h).

Canonical CoProd: ProdCategory :=
  ProdCategory.Pack (co C) CoProd_mixin.
End CoProd.

Section CoCoprod.
Context (C: ProdCategory).

Program Definition CoCoprod_mixin: CoprodCategory.mixin_of (co C) :=
  CoprodCategory.Mixin (co C) prod (fun a b c => @fork C c a b) (@π₁ C) (@π₂ C) (fun a b c f g h => @fork_pi C c a b f g h).

Canonical CoCoprod: CoprodCategory :=
  CoprodCategory.Pack (co C) CoCoprod_mixin.
End CoCoprod.

Section TopCo.
Context (C: Category) (m: BotCategory.mixin_of (co C)).
Let C' := BotCategory.Pack (co C) m.

Definition TopCo_mixin: TopCategory.mixin_of C :=
  TopCategory.Mixin C (0: C') (@from_zero C') (@from_zero_unique C').

Definition TopCo: TopCategory :=
  TopCategory.Pack C TopCo_mixin.
End TopCo.

Section BotCo.
Context (C: Category) (m: TopCategory.mixin_of (co C)).
Let C' := TopCategory.Pack (co C) m.

Definition BotCo_mixin: BotCategory.mixin_of C :=
  BotCategory.Mixin C (1: C') (@to_one C') (@to_one_unique C').

Definition BotCo: BotCategory :=
  BotCategory.Pack C BotCo_mixin.
End BotCo.

Section ProdCo.
Context (C: Category) (m: CoprodCategory.mixin_of (co C)).
Let C' := CoprodCategory.Pack (co C) m.

Program Definition ProdCo_mixin: ProdCategory.mixin_of C :=
  ProdCategory.Mixin C (@coprod C') (fun a b c => @merge C' b c a) (@in1 C') (@in2 C') (fun a b c f g h => @merge_in C' b c a f g h).

Definition ProdCo: ProdCategory :=
  ProdCategory.Pack C ProdCo_mixin.
End ProdCo.

Section CoprodCo.
Context (C: Category) (m: ProdCategory.mixin_of (co C)).
Let C' := ProdCategory.Pack (co C) m.

Program Definition CoprodCo_mixin: CoprodCategory.mixin_of C :=
  CoprodCategory.Mixin C (@prod C') (fun a b c => @fork C' c a b) (@π₁ C') (@π₂ C') (fun a b c f g h => @fork_pi C' c a b f g h).

Definition CoprodCo: CoprodCategory :=
  CoprodCategory.Pack C CoprodCo_mixin.
End CoprodCo.
