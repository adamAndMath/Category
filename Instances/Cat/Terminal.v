Require Export Structure.

Lemma unit_unique (u: unit): tt = u.
Proof. now destruct u. Qed.

Lemma unit_eq (x y: unit): x = y.
Proof. now destruct x, y. Qed.

Definition ONE_mixin: Category.mixin_of unit :=
  Category.Mixin unit (fun _ _ => unit)
  (fun _ => tt) (fun _ _ _ _ _ => tt)
  (fun _ _ _ _ _ _ _ => eq_refl)
  (fun _ _ => unit_unique)
  (fun _ _ => unit_unique).

Canonical ONE: Category :=
  Category.Pack unit ONE_mixin.

Lemma to_ONE_unique (C: Category) (F: C ~> ONE): Δ tt = F.
Proof.
  fun_eq x y f.
  apply unit_unique.
  apply unit_eq.
Qed.

Definition CatTop_mixin: TopCategory.mixin_of Cat :=
  TopCategory.Mixin Cat ONE (fun C => @Δ ONE C tt) to_ONE_unique.

Canonical CatTop: TopCategory :=
  TopCategory.Pack Cat CatTop_mixin.

Definition ONE_Top_mixin: TopCategory.mixin_of 1 :=
  TopCategory.Mixin 1 tt (fun _ => tt) (fun _ => unit_unique).

Canonical ONE_Top: TopCategory :=
  TopCategory.Pack 1 ONE_Top_mixin.

Definition ONE_Bot_mixin: BotCategory.mixin_of 1 :=
  BotCategory.Mixin 1 tt (fun _ => tt) (fun _ => unit_unique).

Canonical ONE_Bot: BotCategory :=
  BotCategory.Pack 1 ONE_Bot_mixin.

Lemma ONE_fork_pi (a b c: ONE) (f: a ~> b) (g: a ~> c) (h: a ~> tt): h = tt <-> tt = f /\ tt = g.
Proof.
  split.
  all: intros _.
  split.
  3: symmetry.
  all: apply unit_unique.
Qed.

Definition ONE_Prod_mixin: ProdCategory.mixin_of 1 :=
  ProdCategory.Mixin 1 (fun _ _ => tt)
  (fun _ _ _ _ _ => tt) (fun _ _ => tt) (fun _ _ => tt)
  ONE_fork_pi.

Canonical ONE_Prod: ProdCategory :=
  ProdCategory.Pack 1 ONE_Prod_mixin.

Lemma ONE_merge_in (a b c: ONE) (f: a ~> c) (g: b ~> c) (h: tt ~> c): h = tt <-> tt = f /\ tt = g.
Proof.
  split.
  all: intros _.
  split.
  3: symmetry.
  all: apply unit_unique.
Qed.

Definition ONE_Coprod_mixin: CoprodCategory.mixin_of 1 :=
  CoprodCategory.Mixin 1 (fun _ _ => tt)
  (fun _ _ _ _ _ => tt) (fun _ _ => tt) (fun _ _ => tt)
  ONE_fork_pi.

Canonical ONE_Coprod: CoprodCategory :=
  CoprodCategory.Pack 1 ONE_Coprod_mixin.
