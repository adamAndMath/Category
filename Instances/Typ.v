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
  all: unfold comp; simpl; unfold tfork.
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
  all: unfold comp; simpl; unfold tmerge.
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
  all: unfold tfork, teval, ttranspose; simpl.
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

Definition teqz {A B: Type} (f g: A -> B) (x: { x | f x = g x }): A := proj1_sig x.

Lemma teqz_comm {A B: Type} (f g: A -> B): @comp Typ _ _ _ f (teqz f g) = @comp Typ _ _ _ g (teqz f g).
Proof.
  extensionality x.
  exact (proj2_sig x).
Qed.

Definition teqz_med {A B C: Type} (f g: B -> C) (e: A -> B) (H: @comp Typ _ _ _ f e = @comp Typ _ _ _ g e) (x: A): { x | f x = g x} :=
  exist _ (e x) (f_equal (fun f => f x) H).

Lemma teqz_med_comm {A B C: Type} (f g: B -> C) (e: A -> B) (H: @comp Typ _ _ _ f e = @comp Typ _ _ _ g e): @comp Typ _ _ _ (teqz f g) (teqz_med f g e H) = e.
Proof. now extensionality x. Qed.

Lemma teqz_med_unique {A B C: Type} (f g: B -> C) (e: A -> B) (u: A -> { x | f x = g x}) (H: @comp Typ _ _ _ f e = @comp Typ _ _ _ g e): @comp Typ _ _ _ (teqz f g) u = e -> teqz_med f g e H = u.
Proof.
  intros He.
  subst e.
  extensionality x.
  now apply eq_sig.
Qed.

Definition TypEq_mixin: EqCategory.mixin_of Typ :=
  EqCategory.Mixin Typ _ (@teqz) (@teqz_comm) (@teqz_med) (@teqz_med_comm) (@teqz_med_unique).

Canonical TypEq: EqCategory :=
  EqCategory.Pack Typ TypEq_mixin.

Program Definition TypSProd_mixin := SProdCategory.Mixin Typ
  (fun I F => forall i, F i)
  (fun I T F f x i => f i x)
  (fun I F i x => x i)
  _.
Next Obligation.
  split.
  + intros H.
    now subst g.
  + intros H.
    extensionality x.
    extensionality i.
    specialize (H i).
    now apply (f_equal (fun f => f x)) in H.
Qed.

Canonical TypSProd: SProdCategory :=
  SProdCategory.Pack Typ TypSProd_mixin.

Program Definition TypSCoprod_mixin := SCoprodCategory.Mixin Typ
  sigT
  (fun I T F f x => f (projT1 x) (projT2 x))
  existT
  _.
Next Obligation.
  split.
  + intros H.
    now subst g.
  + intros H.
    extensionality x.
    destruct x as [i x]; simpl.
    specialize (H i).
    now apply (f_equal (fun f => f x)) in H.
Qed.

Canonical TypSCoprod: SCoprodCategory :=
  SCoprodCategory.Pack Typ TypSCoprod_mixin.

End Typ.

Lemma typ_iso_0 A: A ≃ 0 <-> ~inhabited A.
Proof.
  split.
  intros [i] [x].
  destruct (to i x).
  intros H.
  constructor.
  unshelve eexists.
  intros x.
  absurd (inhabited A).
  exact H.
  now constructor.
  exists ¡.
  all: extensionality x.
  destruct H.
  now constructor.
  destruct x.
Qed.

Lemma Typ_monic {A B: Typ} (f: A ~> B): monic f <-> forall x y: A, f x = f y -> x = y.
Proof.
  split.
  + intros Hf x y H.
    specialize (Hf 1 (fun _ => x) (fun _ => y)).
    specialize (fun H => f_equal (fun f => f tt) (Hf H)) as Hf'.
    clear Hf; rename Hf' into Hf.
    apply Hf; clear Hf.
    extensionality z.
    exact H.
  + intros Hf Z a b H.
    extensionality x.
    apply (f_equal (fun f => f x)) in H.
    apply Hf, H.
Qed.

Lemma Typ_epic {A B: Typ} (f: A ~> B): epic f <-> forall y: B, exists x: A, f x = y.
Proof.
  split.
  + intros Hf y.
    destruct (classic (exists x, f x = y)).
    assumption.
    assert (forall x: A, f x <> y) as H'.
      intros x Hx.
      destruct H.
      now exists x.
    specialize (Hf bool
      (fun y' => if dec (y' = y) then true else false)
      (fun _ => false)
    ).
    clear H; rename H' into H.
    assert (
      @comp Typ _ _ _ (fun y' : B => if dec (y' = y) then true else false) f =
      @comp Typ _ _ _ (fun _ : B => false) f
    ).
    extensionality x.
    specialize (H x).
    change ((if dec (f x = y) then true else false) = false).
    now destruct (dec (f x = y)).
    specialize (Hf H0).
    clear H H0.
    apply (f_equal (fun f => f y)) in Hf.
    now destruct (dec (y = y)).
  + intros Hf.
    apply ex_forall in Hf.
    destruct Hf as [g H].
    apply splitepic_is_epic.
    exists g.
    extensionality x.
    apply H.
Qed.

Lemma Typ_splitepic {A B: Typ} (f: A ~> B): epic f -> splitepic f.
Proof.
  intros Hf.
  rewrite Typ_epic in Hf.
  apply ex_forall in Hf.
  destruct Hf as [g H].
  exists g.
  extensionality x.
  apply H.
Qed.

Lemma fobj_splitmonic {S T: Category} (F: S ~> T): splitmonic F -> @splitmonic Typ S T (fobj F).
Proof.
  intros [G H].
  exists (fobj G).
  change (fobj (G ∘ F) = fobj (id S)).
  now f_equal.
Qed.

Lemma fobj_splitepic {S T: Category} (F: S ~> T): splitepic F -> @splitepic Typ S T (fobj F).
Proof.
  intros [G H].
  exists (fobj G).
  change (fobj (F ∘ G) = fobj (id T)).
  now f_equal.
Qed.
