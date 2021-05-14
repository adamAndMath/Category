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

Module TypComp.

Structure obj {C: Category} (F: Functor C Typ) := Obj {
  family x: F x;
  family_comm {x y} f: fmap F f (family x) = family y;
}.

Arguments family {C F} o x.
Arguments family_comm {C F} o {x y} f.
Coercion family: obj >-> Funclass.

Lemma obj_eq {C: Category} {F: Functor C Typ} (X Y: obj F): X = Y <-> forall x, X x = Y x.
Proof.
  split.
  now intros [].
  destruct X as [X HX], Y as [Y HY]; simpl.
  intros H.
  enough (X = Y); [subst Y|].
  f_equal; apply proof_irrelevance.
  now extensionality x.
Qed.

Program Definition Proj {C: Category} {F: Functor C Typ}: @Δ Typ C (obj F) ~> F := {|
  transform x X := X x;
|}.
Next Obligation.
  extensionality X.
  unfold comp, id; simpl.
  symmetry.
  apply family_comm.
Qed.

Program Definition map {C: Category} {F: Functor C Typ} {T: Type} (η: @Δ Typ C T ~> F) (t: T): obj F := {|
  family x := η x t;
|}.
Next Obligation.
  change ((fmap F f ∘ η x) t = η y t).
  apply (f_equal (fun f => f t)).
  rewrite <- (naturality η).
  exact (comp_id_r (η y)).
Qed.

Lemma Proj_map {C: Category} {F: Functor C Typ} {T: Type} (η: @Δ Typ C T ~> F) (X: T) (x: C): Proj x (map η X) = η x X.
Proof. reflexivity. Qed.

End TypComp.

Coercion TypComp.family: TypComp.obj >-> Funclass.

Program Definition TypComp_mixin := Complete.Mixin Typ (@TypComp.obj) (@TypComp.Proj) (@TypComp.map) _ _.
Next Obligation.
  rename X into T.
  natural_eq X.
  now extensionality x.
Qed.
Next Obligation.
  rename X into T.
  extensionality t.
  now apply TypComp.obj_eq.
Qed.

Canonical TypComp := Complete.Pack Typ TypComp_mixin.

Module TypCocomp.

Structure preObj {C: Category} (F: Functor C Typ) := PreObj {
  lobj: C;
  lelm: F lobj;
}.

Arguments PreObj {C F} lobj lelm.
Arguments lobj {C F} _.
Arguments lelm {C F} _.

Inductive equiv {C: Category} {F: Functor C Typ}: preObj F -> preObj F -> Prop :=
  | equiv_path {X Y Z: C} (f: X ~> Y) (g: X ~> Z) (x: F X): equiv (PreObj Y (fmap F f x)) (PreObj Z (fmap F g x))
  | equiv_trans X Y Z: equiv X Y -> equiv Y Z -> equiv X Z.

Instance equiv_inst (C: Category) (F: Functor C Typ): Equivalence (@equiv C F).
Proof.
  split.
  + intros [X x].
    change x with (id (F X) x).
    rewrite <- fmap_id.
    apply equiv_path.
  + intros X Y H.
    induction H.
    apply equiv_path.
    now apply (equiv_trans _ Y).
  + exact equiv_trans.
Qed.

Lemma equiv_step {C: Category} {X Y: C} (F: Functor C Typ) (f: X ~> Y) (x: F X): equiv (PreObj Y (fmap F f x)) (PreObj X x).
Proof.
  change x with (id (F X) x) at 2.
  rewrite <- fmap_id.
  apply equiv_path.
Qed.

Structure obj {C: Category} (F: Functor C Typ) := {
  class: preObj F -> Prop;
  class_inhabited: exists X, forall Y, class Y <-> equiv X Y;
}.

Arguments class {C F} _ _.
Arguments class_inhabited {C F} _.
Coercion class: obj >-> Funclass.

Instance class_proper (C: Category) (F: Functor C Typ): Proper (eq ==> @equiv C F ==> iff) class.
Proof.
  intros P Q e X Y H.
  subst Q.
  destruct (class_inhabited P) as [Z HZ].
  rewrite !HZ.
  now f_equiv.
Qed.

Program Definition Obj {C: Category} {F: Functor C Typ} (X: C) (x: F X) := {|
  class := equiv {| lobj := X; lelm := x |};
|}.
Next Obligation.
  now exists {| lobj := X; lelm := x |}.
Qed.

Lemma obj_eq {C: Category} {F: Functor C Typ} (X Y: obj F): X = Y <-> forall p, X p <-> Y p.
Proof.
  split.
  now intros [].
  destruct X as [X HX], Y as [Y HY]; simpl.
  intros H.
  enough (X = Y); [subst Y|].
  f_equal; apply proof_irrelevance.
  extensionality p.
  now apply propositional_extensionality.
Qed.

Lemma Obj_eq {C: Category} {F: Functor C Typ} (X: C) (x: F X) (Y: obj F): Obj X x = Y <-> Y (PreObj X x).
Proof.
  destruct (class_inhabited Y) as [y H].
  rewrite obj_eq; simpl; split.
  intros Hp.
  now apply Hp.
  intros Hx p.
  apply H in Hx.
  rewrite H.
  now f_equiv.
Qed.

Lemma Obj_surj {C: Category} {F: Functor C Typ} (X: obj F): exists Y (y: F Y), Obj Y y = X.
Proof.
  enough (exists Y (y: F Y), X {| lobj := Y; lelm := y |}) as [Y [y H]].
  exists Y, y.
  now apply Obj_eq.
  destruct X as [P HP]; simpl.
  destruct HP as [[X x] H].
  exists X, x.
  now apply H.
Qed.

Program Definition Into {C: Category} {F: Functor C Typ}: F ~> @Δ Typ C (obj F) := {|
  transform := Obj;
|}.
Next Obligation.
  rename x into X, y into Y.
  rewrite comp_id_l.
  extensionality x.
  unfold comp; simpl.
  apply Obj_eq; simpl.
  change x with (id (F X) x) at 1.
  rewrite <- fmap_id.
  apply equiv_path.
Qed.

Lemma preObj_inhab {C: Category} {F: Functor C Typ} (X: obj F): inhabited (preObj F).
Proof. now destruct (class_inhabited X) as [x _]. Qed.

Definition map {C: Category} {F: Functor C Typ} {T: Type} (η: F ~> @Δ Typ C T) (X: obj F): T :=
  η (lobj (epsilon (preObj_inhab X) X)) (lelm (epsilon (preObj_inhab X) X)).

Lemma map_Obj {C: Category} {F: Functor C Typ} {T: Type} (η: F ~> @Δ Typ C T) (X: C) (x: F X): map η (Obj X x) = η X x.
Proof.
  unfold map.
  generalize (epsilon (preObj_inhab (Obj X x)) (Obj X x)), (epsilon_spec (preObj_inhab (Obj X x)) (Obj X x)).
  intros p H.
  assert (exists Y, Obj X x Y) by now exists (PreObj X x); simpl.
  specialize (H H0); clear H0.
  simpl in H.
  set (PreObj X x) in H.
  change X with (lobj p0).
  change x with (lelm p0).
  clearbody p0; clear X x.
  induction H; simpl.
  transitivity (η X x).
  2: symmetry.
  1: change ((η Z ∘ fmap F g) x = (fmap (Δ T) g ∘ η X) x).
  2: change ((η Y ∘ fmap F f) x = (fmap (Δ T) f ∘ η X) x).
  1, 2: apply (f_equal (fun f => f _)).
  1, 2: apply (naturality η).
  now transitivity (η (lobj Y) (lelm Y)).
Qed.

End TypCocomp.

Program Definition TypCocomp_mixin := Cocomplete.Mixin Typ (@TypCocomp.obj) (@TypCocomp.Into) (@TypCocomp.map) _ _.
Next Obligation.
  rename X into T.
  natural_eq X.
  extensionality x.
  unfold comp; simpl.
  apply TypCocomp.map_Obj.
Qed.
Next Obligation.
  rename X into T.
  extensionality P.
  destruct (TypCocomp.Obj_surj P) as [X [x H]].
  subst P.
  apply TypCocomp.map_Obj.
Qed.

Canonical TypCocomp := Cocomplete.Pack Typ TypCocomp_mixin.

Lemma Colim_map_TypObj {D} (F G: Functor D Typ) (η: F ~> G) (X: D) (x: F X): Colim_map η (TypCocomp.Obj X x) = TypCocomp.Obj X (η X x).
Proof.
  change ((Colim_map η ∘ Colim F X) x = (Colim G X ∘ η X) x).
  apply (f_equal (fun f => f x)).
  exact (Colim_map_Colim η X).
Qed.

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
