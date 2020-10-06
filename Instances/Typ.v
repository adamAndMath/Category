Require Export Structure.
Require Export Categories.Typ.

Section Typ.
Let T := Type.

Definition to_unit {A: T} (x: A) := tt.

Lemma to_unit_unique {A: T} (f: A -> unit): to_unit = f.
Proof.
  extensionality x.
  now destruct (f x).
Qed.

Definition TypTop_mixin: TopCategory.mixin_of Typ :=
  TopCategory.Mixin Typ unit (@to_unit) (@to_unit_unique).

Canonical TypTop: TopCategory :=
  TopCategory.Pack Typ TypTop_mixin.

Definition from_empty {A: T}: Empty_set -> A := Empty_set_rect (fun _ => A).

Lemma from_empty_unique {A: T} (f: Empty_set -> A): from_empty = f.
Proof.
  extensionality x.
  destruct x.
Qed.

Definition TypBot_mixin: BotCategory.mixin_of Typ :=
  BotCategory.Mixin Typ Empty_set (@from_empty) (@from_empty_unique).

Canonical TypBot: BotCategory :=
  BotCategory.Pack Typ TypBot_mixin.

Definition tfork {A B C: T} (f: A -> B) (g: A -> C) (x: A): B * C := (f x, g x).

Lemma tfork_pi {A B C: T} (f: A -> B) (g: A -> C) (h: A -> B * C): h = tfork f g <-> @comp Typ _ _ _ fst h = f /\ @comp Typ _ _ _ snd h = g.
Proof.
  split.
  1: intros H.
  1: subst h.
  2: intros [Hf Hg].
  2: subst f g.
  split.
  all: extensionality x.
  all: unfold comp; simpl; unfold Typ.comp, tfork.
  all: simpl.
  1, 2: reflexivity.
  now destruct (h x).
Qed.

Definition TypProd_mixin: ProdCategory.mixin_of Typ :=
  ProdCategory.Mixin Typ _ (@tfork) (@fst) (@snd) (@tfork_pi).

Canonical TypProd: ProdCategory :=
  ProdCategory.Pack Typ TypProd_mixin.

Definition tmerge {A B C: T} (f: A -> C) (g: B -> C) (x: A + B): C :=
  match x with
  | inl x => f x
  | inr x => g x
  end.

Lemma tmerge_in {A B C: T} (f: A -> C) (g: B -> C) (h: A + B -> C): h = tmerge f g <-> @comp Typ _ _ _ h inl = f /\ @comp Typ _ _ _ h inr = g.
Proof.
  split.
  1: intros H.
  1: subst h.
  2: intros [Hf Hg].
  2: subst f g.
  split.
  all: extensionality x.
  all: unfold comp; simpl; unfold Typ.comp, tmerge.
  1, 2: reflexivity.
  now destruct x.
Qed.

Definition TypCoprod_mixin: CoprodCategory.mixin_of Typ :=
  CoprodCategory.Mixin Typ _ (@tmerge) (@inl) (@inr) (@tmerge_in).

Canonical TypCoprod: CoprodCategory :=
  CoprodCategory.Pack Typ TypCoprod_mixin.

Definition teval {B A: T} (p: (A -> B) * A): B :=
  fst p (snd p).

Definition ttranspose {C B A: T} (f: A * B -> C) (x: A) (y: B): C := f (x, y).

Lemma ttranspose_ump {C B A: T} (f: A * B -> C) (g: A -> B -> C): @comp Typ _ _ _ teval (@fprod TypProd _ _ _ _ g (id B)) = f <-> ttranspose f = g.
Proof.
  split; intros H.
  1: subst f.
  2: subst g.
  all: extensionality x.
  extensionality y.
  all: unfold fprod, fork, pi1, pi2, comp, id; simpl.
  all: unfold Typ.id, Typ.comp, tfork, teval, ttranspose; simpl.
  reflexivity.
  now destruct x.
Qed.

Definition TypExp_mixin: ExpCategory.mixin_of TypProd :=
  ExpCategory.Mixin TypProd _ (@teval) (@ttranspose) (@ttranspose_ump).

Canonical TypExp: ExpCategory :=
  ExpCategory.Pack Typ (ExpCategory.Class Typ TypProd_mixin TypExp_mixin).

Canonical TypCart: CartCategory :=
  CartCategory.Pack Typ (CartCategory.Class Typ TypTop_mixin TypProd_mixin).

Canonical TypCCC: CCC :=
  CCC.Pack Typ (CCC.Class Typ (CartCategory.class TypCart) TypExp_mixin).

End Typ.
