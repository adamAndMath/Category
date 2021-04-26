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

Lemma to_ONE_unique (C: Category) (F: Functor C ONE): Δ tt = F.
Proof.
  fun_eq x y f.
  apply unit_unique.
  apply unit_eq.
Qed.

Definition CatTop_mixin: TopCategory.mixin_of Cat :=
  TopCategory.Mixin Cat ONE (fun C => @Δ ONE C tt) to_ONE_unique.

Canonical CatTop: TopCategory :=
  TopCategory.Pack Cat CatTop_mixin.

Definition CoOne_from: Functor ONE (co ONE) := {|
  fobj x := x;
  fmap x y f := f;
  fmap_id _ := eq_refl;
  fmap_comp _ _ _ _ _ := eq_refl;
|}.

Lemma CoOne_inv_l: ! ∘ CoOne_from = id 1.
Proof.
  fun_eq x y f.
  apply unit_unique.
  apply unit_eq.
Qed.

Lemma CoOne_inv_r: CoOne_from ∘ ! = id (co 1).
Proof.
  fun_eq x y f.
  apply unit_unique.
  apply unit_eq.
Qed.

Definition CoOne: co 1 <~> 1 :=
  Isomorphism.Pack ! (Isomorphism.Mixin _ _ _ ! CoOne_from CoOne_inv_l CoOne_inv_r).

Lemma co_1: co 1 ≃ 1.
Proof.
  constructor.
  exact CoOne.
Qed.

Definition ONE_Top_mixin: TopCategory.mixin_of ONE :=
  TopCategory.Mixin ONE tt (fun _ => tt) (fun _ => unit_unique).

Canonical ONE_Top: TopCategory :=
  TopCategory.Pack ONE ONE_Top_mixin.

Definition ONE_Bot_mixin: BotCategory.mixin_of ONE :=
  BotCategory.Mixin ONE tt (fun _ => tt) (fun _ => unit_unique).

Canonical ONE_Bot: BotCategory :=
  BotCategory.Pack ONE ONE_Bot_mixin.

Lemma ONE_fork_pi (a b c: ONE) (f: a ~> b) (g: a ~> c) (h: a ~> tt): h = tt <-> tt = f /\ tt = g.
Proof.
  split.
  all: intros _.
  split.
  3: symmetry.
  all: apply unit_unique.
Qed.

Definition ONE_Prod_mixin: ProdCategory.mixin_of ONE :=
  ProdCategory.Mixin ONE (fun _ _ => tt)
  (fun _ _ _ _ _ => tt) (fun _ _ => tt) (fun _ _ => tt)
  ONE_fork_pi.

Canonical ONE_Prod: ProdCategory :=
  ProdCategory.Pack ONE ONE_Prod_mixin.

Lemma ONE_merge_in (a b c: ONE) (f: a ~> c) (g: b ~> c) (h: tt ~> c): h = tt <-> tt = f /\ tt = g.
Proof.
  split.
  all: intros _.
  split.
  3: symmetry.
  all: apply unit_unique.
Qed.

Definition ONE_Coprod_mixin: CoprodCategory.mixin_of ONE :=
  CoprodCategory.Mixin ONE (fun _ _ => tt)
  (fun _ _ _ _ _ => tt) (fun _ _ => tt) (fun _ _ => tt)
  ONE_fork_pi.

Canonical ONE_Coprod: CoprodCategory :=
  CoprodCategory.Pack ONE ONE_Coprod_mixin.

Lemma ONE_transpose_ump (t s x: ONE) (f: x × s ~> t) (g: x ~> tt): tt = f <-> tt = g.
Proof.
  now destruct f, g.
Qed.

Definition ONE_Exp_mixin: ExpCategory.mixin_of ONE_Prod :=
  ExpCategory.Mixin ONE_Prod (fun _ _ => tt) (fun _ _ => tt) (fun _ _ _ _ => tt) ONE_transpose_ump.

Canonical ONE_Exp := ExpCategory.Pack ONE (ExpCategory.Class ONE ONE_Prod_mixin ONE_Exp_mixin).
