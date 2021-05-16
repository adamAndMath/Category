Require Export Structure.
Require Export Categories.Typ.

Module Proset.

Module obj.

Structure mixin_of T := Mixin {
  le: T -> T -> Prop;
  le_preorder: PreOrder le;
}.

Lemma mixin_eq {T} (c d: mixin_of T): c = d <-> forall x y, le T c x y <-> le T d x y.
Proof.
  split.
  now intros [].
  destruct c as [R1 H1], d as [R2 H2]; simpl.
  intros H.
  enough (R1 = R2); [subst R2|].
  f_equal; apply proof_irrelevance.
  extensionality x.
  extensionality y.
  apply propositional_extensionality.
  apply H.
Qed.

Structure type := Pack { sort: Type; _: mixin_of sort }.

Notation class_of := mixin_of (only parsing).

Section ClassDef.
Local Coercion sort: type >-> Sortclass.

Variable (T: type).
Definition class := match T return mixin_of T with Pack _ c => c end.

Let xT := match T with Pack T _ => T end.
Notation xclass := (class: mixin_of xT).

End ClassDef.

Module Exports.
Coercion sort: type >-> Sortclass.

Definition le {T: type}: T -> T -> Prop := le T (class T).
Instance le_preorder {T: type}: PreOrder le := le_preorder T (class T).
Infix "<=" := le.

End Exports.
End obj.
Export obj.Exports.
Notation obj := obj.type.

Structure hom (S T: obj) := Hom {
  map: S -> T;
  monotone: forall x y, x <= y -> map x <= map y;
}.

Arguments map {S T} h s.
Arguments monotone {S T} h x y H.
Coercion map: hom >-> Funclass.

Lemma hom_eq {S T: obj} (f g: hom S T): f = g <-> forall x, f x = g x.
Proof.
  split.
  now intros [].
  destruct f as [f Hf], g as [g Hg]; simpl.
  intros H.
  enough (f = g); [subst g|].
  f_equal; apply proof_irrelevance.
  now extensionality x.
Qed.

Program Definition cat_mixin := Category.Mixin obj hom
  (fun P => {|
    map x := x;
    monotone x y H := H;
  |})
  (fun X Y Z f g => {|
    map x := f (g x);
    monotone x y H := monotone f _ _ (monotone g x y H);
  |}) _ _ _.
Next Obligation.
  now apply hom_eq.
Qed.
Next Obligation.
  now apply hom_eq.
Qed.
Canonical cat := Category.Pack obj cat_mixin.

Program Definition exp_mixin (T S: obj) := obj.Mixin (hom S T) (fun f g => forall x, f x <= g x) _.
Next Obligation.
  split.
  easy.
  intros f g h H1 H2 x.
  now transitivity (g x).
Qed.
Canonical exp (T S: obj) := obj.Pack (hom S T) (exp_mixin T S).

Instance map_monotone S T: Proper (le ==> le ==> le) (@map S T).
Proof.
  intros f g Hf x y Hx.
  rewrite <- (Hf y).
  now apply monotone.
Qed.

Program Definition dual_mixin (P: obj) := obj.Mixin P (fun x y => y <= x) _.
Next Obligation.
  split.
  easy.
  intros x y z H1 H2.
  now transitivity y.
Qed.
Definition dual (P: obj) := obj.Pack P (dual_mixin P).

Program Definition dual_map {S T: obj} (f: S ~> T): dual S ~> dual T := {|
  map x := f x;
  monotone x y H := monotone f y x H;
|}.

Program Canonical Dual: Functor cat cat := {|
  fobj := dual;
  fmap := @dual_map;
|}.

Lemma dual_invol (P: obj): dual (dual P) = P.
Proof.
  destruct P as [T c].
  unfold dual; simpl.
  f_equal.
  now apply obj.mixin_eq.
Qed.

Lemma Dual_invol: Dual ∘ Dual = id cat.
Proof.
  fun_eq X Y f.
  apply dual_invol.
  apply hom_eq; simpl.
  revert H H0.
  destruct X as [X [R1 H1]], Y as [Y [R2 H2]], f as [f Hf]; simpl in *.
  unfold dual, dual_mixin, le; simpl.
  replace (dual_mixin_obligation_1
  (obj.Pack X
     {|
     obj.le := fun x y : X => R1 y x;
     obj.le_preorder := dual_mixin_obligation_1
                     (obj.Pack X
                     {|
                     obj.le := R1;
                     obj.le_preorder := H1 |}) |})) with H1
    by apply proof_irrelevance.
  replace (dual_mixin_obligation_1
  (obj.Pack Y
     {|
     obj.le := fun x y : Y => R2 y x;
     obj.le_preorder := dual_mixin_obligation_1
                     (obj.Pack Y
                     {|
                     obj.le := R2;
                     obj.le_preorder := H2 |}) |})) with H2
    by apply proof_irrelevance.
  intros H H0 x.
  now rewrite !eq_iso_refl.
Qed.

Program Definition empty_mixin := obj.Mixin Empty_set (fun _ _ => True) _.
Next Obligation. easy. Qed.
Canonical empty := obj.Pack Empty_set empty_mixin.

Program Definition botCat_mixin := BotCategory.Mixin cat empty
  (fun P => {|
    map := Empty_set_rect (fun _ => P);
  |}) _.
Next Obligation.
  contradiction.
Qed.
Next Obligation.
  now apply hom_eq.
Qed.
Canonical botCat := BotCategory.Pack cat botCat_mixin.

Program Definition unit_mixin := obj.Mixin unit (fun _ _ => True) _.
Next Obligation. easy. Qed.
Canonical unit := obj.Pack unit unit_mixin.

Program Definition topCat_mixin := TopCategory.Mixin cat unit
  (fun P => {|
    map _ := tt;
  |}) _.
Next Obligation.
  reflexivity.
Qed.
Next Obligation.
  apply hom_eq; simpl.
  intros x.
  now destruct (f x).
Qed.
Canonical topCat := TopCategory.Pack cat topCat_mixin.

Program Definition sum_mixin (A B: obj) := obj.Mixin (A + B) (fun p q =>
  match p, q with
  | inl x, inl y => x <= y
  | inr x, inr y => x <= y
  | inl _, inr _ | inr _, inl _ => False
  end) _.
Next Obligation.
  split.
  now intros [x | x].
  intros [x|x] [y|y] [z|z]; try easy.
  all: apply transitivity.
Qed.
Canonical sum (A B: obj) := obj.Pack (A + B) (sum_mixin A B).

Program Canonical inl {A B: obj} := {|
  map := @inl A B;
|}.

Program Canonical inr {A B: obj} := {|
  map := @inr A B;
|}.

Program Canonical merge {X Y Z: obj} (f: hom X Z) (g: hom Y Z) := {|
  map := sum_rect (fun _ => Z) f g;
|}.
Next Obligation.
  destruct x as [x|x], y as [y|y]; simpl.
  2, 3: contradiction.
  all: now apply monotone.
Qed.

Program Definition coprodCat_mixin := CoprodCategory.Mixin cat sum
  (@merge) (@inl) (@inr) _.
Next Obligation.
  split.
  + intros H.
    subst h.
    split.
    all: now apply hom_eq.
  + intros [].
    subst f g.
    apply hom_eq; simpl.
    now intros [].
Qed.
Canonical coprodCat := CoprodCategory.Pack cat coprodCat_mixin.

Program Definition prod_mixin (A B: obj) := obj.Mixin (A * B) (fun p q => fst p <= fst q /\ snd p <= snd q) _.
Next Obligation.
  split.
  + intros p.
    now split.
  + intros p q r H1 H2.
    split.
    now transitivity (fst q).
    now transitivity (snd q).
Qed.
Canonical prod (A B: obj) := obj.Pack (A * B) (prod_mixin A B).

Program Canonical fst {A B: obj} := {|
  map := @fst A B;
|}.
Next Obligation.
  apply H.
Qed.

Program Canonical snd {A B: obj} := {|
  map := @snd A B;
|}.
Next Obligation.
  apply H.
Qed.

Program Definition prodCat_mixin := ProdCategory.Mixin cat prod
  (fun X Y Z f g => {|
    map x := (f x, g x);
  |}) (@fst) (@snd) _.
Next Obligation.
  now split; simpl; apply monotone.
Qed.
Next Obligation.
  split.
  + intros H.
    subst h.
    split.
    all: now apply hom_eq.
  + intros [].
    subst f g.
    apply hom_eq; simpl.
    intros x.
    now destruct (h x).
Qed.
Canonical prodCat := ProdCategory.Pack cat prodCat_mixin.

Program Definition sigT_mixin {I} (F: I -> obj) := obj.Mixin (sigT F) (fun x y => exists (e: projT1 x = projT1 y), match e in _ = z return F z with eq_refl => projT2 x end <= projT2 y) _.
Next Obligation.
  split.
  + intros [i x].
    now exists eq_refl.
  + intros [i x] [j y] [k z] [e1 H1] [e2 H2]; simpl in *.
    subst j k.
    exists eq_refl.
    now transitivity y.
Qed.
Canonical sigT {I} (F: I -> obj) := obj.Pack (sigT F) (sigT_mixin F).

Program Canonical existT {I} (F: I -> obj) (i: I) := {|
  map := existT F i;
|}.
Next Obligation.
  now exists eq_refl.
Qed.

Program Canonical sigT_map {I} {P: obj} {F: I -> obj} (f: forall i, hom (F i) P) := {|
  map := sigT_rect (fun _ => P) f;
|}.
Next Obligation.
  destruct H as [e H]; simpl in *.
  subst y.
  now apply monotone.
Qed.

Program Definition scoprodCat_mixin := SCoprodCategory.Mixin cat (@sigT) (@sigT_map) (@existT) _.
Next Obligation.
  split.
  + intros H.
    subst g.
    intros i.
    now apply hom_eq.
  + intros H.
    apply functional_extensionality_dep in H.
    subst f.
    apply hom_eq; simpl.
    now intros [i x].
Qed.
Canonical scoprodCat := SCoprodCategory.Pack cat scoprodCat_mixin.

Program Definition Prod_mixin {I} (F: I -> obj) := obj.Mixin (forall i, F i) (fun f g => forall i, f i <= g i) _.
Next Obligation.
  split.
  easy.
  intros f g h H1 H2 i.
  now transitivity (g i).
Qed.
Definition Prod {I} (F: I -> obj) := obj.Pack (forall i, F i) (Prod_mixin F).

Program Definition sprodCat_mixin := SProdCategory.Mixin cat
  (@Prod)
  (fun I T F f => {|
    map x i := f i x;
  |})
  (fun I F i => {|
    map x := x i;
  |}) _.
Next Obligation.
  intros i.
  now apply monotone.
Qed.
Next Obligation.
  split.
  + intros H.
    subst g.
    intros i.
    now apply hom_eq.
  + intros H.
    apply functional_extensionality_dep in H.
    subst f.
    now apply hom_eq.
Qed.
Canonical sprodCat := SProdCategory.Pack cat sprodCat_mixin.

Definition cartCat_class := CartCategory.Class cat topCat_mixin prodCat_mixin.
Canonical cartCat := CartCategory.Pack cat cartCat_class.

Program Definition expCat_mixin := ExpCategory.Mixin prodCat
  exp
  (fun T S => {|
    map p := fst p (snd p);
  |})
  (fun T S P => {|
    map (f: (P × S) ~> T) := {|
      map x := {|
        map y := f (x, y);
      |};
    |};
  |}) _.
Next Obligation.
  destruct H as [Hh Hs]; simpl in *.
  now rewrite Hs.
Qed.
Next Obligation.
  now apply monotone.
Qed.
Next Obligation.
  intros z; simpl.
  now apply monotone.
Qed.
Next Obligation.
  intros f z; simpl.
  apply H.
Qed.
Next Obligation.
  split.
  + intros H.
    subst f.
    apply hom_eq; simpl.
    intros a.
    now apply hom_eq; simpl.
  + intros H.
    subst g.
    apply hom_eq; simpl.
    now intros [].
Qed.
Definition expCat_class := ExpCategory.Class cat prodCat_mixin expCat_mixin.
Canonical expCat := ExpCategory.Pack cat expCat_class.

Definition CCC_class := CCC.Class cat cartCat_class expCat_mixin.
Canonical CCC := CCC.Pack cat CCC_class.

Program Canonical Forget: Functor cat Typ := {|
  fobj := obj.sort;
  fmap := @map;
|}.

Definition discrete_mixin T := obj.Mixin T eq _.
Definition discrete T := obj.Pack T (discrete_mixin T).

Definition discrete_map {S T} (f: S -> T) :=
  Hom (discrete S) (discrete T) f (f_equal f).

Program Canonical Discrete := {|
  fobj := discrete;
  fmap := @discrete_map;
|}.
Next Obligation.
  now apply hom_eq.
Qed.
Next Obligation.
  now apply hom_eq.
Qed.

Program Definition discreteU: id Typ ~> Forget ∘ Discrete := {|
  transform T x := x;
|}.

Program Definition discrete_counit (P: obj): discrete P ~> P := {|
  map x := x;
|}.
Next Obligation.
  now destruct H.
Qed.

Program Canonical discreteCU: Discrete ∘ Forget ~> id cat := {|
  transform := discrete_counit;
|}.
Next Obligation.
  now apply hom_eq.
Qed.

Lemma discrete_adjoint: adjoint_by Discrete Forget discreteU discreteCU.
Proof.
  apply adjoint_by_alt; split.
  + intros T.
    now apply hom_eq.
  + intros P.
    now extensionality x.
Qed.

Program Definition indiscrete_mixin T := obj.Mixin T (fun _ _ => True) _.
Next Obligation. easy. Qed.
Definition indiscrete T := obj.Pack T (indiscrete_mixin T).

Definition indiscrete_map {S T} (f: S -> T) :=
  Hom (indiscrete S) (indiscrete T) f (fun _ _ _ => I).

Program Canonical Indiscrete := {|
  fobj := indiscrete;
  fmap := @indiscrete_map;
|}.
Next Obligation.
  now apply hom_eq.
Qed.

Definition indiscrete_unit (P: obj): P ~> indiscrete P :=
  Hom P (indiscrete P) (fun x => x) (fun _ _ _ => I).

Program Canonical indiscreteU: id cat ~> Indiscrete ∘ Forget := {|
  transform := indiscrete_unit;
|}.

Program Definition indiscreteCU: Forget ∘ Indiscrete ~> id Typ := {|
  transform T x := x;
|}.

Lemma indiscrete_adjoint: adjoint_by Forget Indiscrete indiscreteU indiscreteCU.
Proof.
  apply adjoint_by_alt.
  split.
  + intros P.
    now extensionality x.
  + intros T.
    now apply hom_eq.
Qed.

Program Definition category_mixin (P: obj) := Category.Mixin P le reflexivity (fun _ _ _ f g => transitivity g f) _ _ _.
Next Obligation.
  apply proof_irrelevance.
Qed.
Next Obligation.
  apply proof_irrelevance.
Qed.
Next Obligation.
  apply proof_irrelevance.
Qed.
Canonical category (P: obj) := Category.Pack P (category_mixin P).
Coercion category: obj >-> Category.

Lemma chom_eq {P: obj} {x y: P} (f g: x ~> y): f = g.
Proof. exact (proof_irrelevance (le x y) f g). Qed.

Program Canonical hom_func {P Q: obj} (f: hom P Q) := {|
  fobj := f;
  fmap := monotone f;
|}.
Next Obligation.
  apply chom_eq.
Qed.
Next Obligation.
  apply chom_eq.
Qed.
Coercion hom_func: hom >-> Functor.

Program Canonical Cat: Functor cat Cat := {|
  fobj := category;
  fmap := @hom_func;
|}.
Next Obligation.
  now fun_eq x y f.
Qed.
Next Obligation.
  now fun_eq x y h.
Qed.

Program Definition conn_mixin (C: Category) := obj.Mixin C (fun x y => inhabited (x ~> y)) _.
Next Obligation.
  split.
  + intros x.
    constructor.
    exact (id x).
  + intros x y z [f] [g].
    constructor.
    exact (g ∘ f).
Qed.
Definition conn (C: Category) := obj.Pack C (conn_mixin C).

Program Definition conn_map {S T: Category} (F: Functor S T): conn S ~> conn T := {|
  map := F;
|}.
Next Obligation.
  destruct H as [f].
  constructor.
  exact (fmap F f).
Qed.

Program Canonical Conn: Functor Functor.Cat cat := {|
  fobj := conn;
  fmap := @conn_map;
|}.
Next Obligation.
  now apply hom_eq.
Qed.
Next Obligation.
  now apply hom_eq.
Qed.

Program Definition Conn_unit (C: Category): Functor C (conn C) := {|
  fobj x := x;
  fmap x y := @inhabits _;
|}.
Next Obligation.
  apply chom_eq.
Qed.
Next Obligation.
  apply chom_eq.
Qed.

Program Canonical ConnU: id Functor.Cat ~> Cat ∘ Conn := {|
  transform := Conn_unit;
|}.
Next Obligation.
  rename x into S, y into T, f into F.
  fun_eq x y f.
  apply chom_eq.
Qed.

Program Definition Conn_counit (P: obj): conn P ~> P := {|
  map x := x;
|}.
Next Obligation.
  now destruct H.
Qed.

Program Canonical ConnCU: Conn ∘ Cat ~> id cat := {|
  transform := Conn_counit;
|}.
Next Obligation.
  now apply hom_eq.
Qed.

Lemma Conn_adjoint: adjoint_by Conn Cat ConnU ConnCU.
Proof.
  apply adjoint_by_alt.
  split.
  + intros C.
    now apply hom_eq.
  + intros P.
    fun_eq x y f.
    apply chom_eq.
Qed.

Lemma iso_alt {P: obj} (x y: P): x ≃ y <-> x <= y /\ y <= x.
Proof.
  split.
  + intros [i].
    split.
    exact (to i).
    exact (from i).
  + intros [f g].
    constructor.
    exists f, g.
    all: apply chom_eq.
Qed.

Instance le_respect_iso (P: obj): Proper (isomorphic P ==> isomorphic P ==> iff) le.
Proof.
  enough (Proper (isomorphic P ==> isomorphic P ==> impl) le).
  now split; apply H.
  intros x1 x2 Hx y1 y2 Hy H.
  rewrite iso_alt in Hx, Hy.
  now rewrite (proj2 Hx), <- (proj1 Hy).
Qed.

Instance map_iso S T: Proper (isomorphic (exp T S) ==> isomorphic S ==> isomorphic T) (@map S T).
Proof.
  intros f g Hf x y Hx.
  apply iso_alt in Hf.
  apply iso_alt in Hx.
  apply iso_alt.
  split.
  1: rewrite <- (proj1 Hf y).
  2: rewrite (proj2 Hf y).
  all: now apply monotone.
Qed.

End Proset.

Export Proset.obj.Exports.
Notation Proset := Proset.cat.
Coercion Proset.map: Proset.hom >-> Funclass.
Coercion Proset.category: Proset.obj >-> Category.
Coercion Proset.hom_func: Proset.hom >-> Functor.
Canonical Proset.empty.
Canonical Proset.unit.
Canonical Proset.sum.
Canonical Proset.prod.
Canonical Proset.sigT.
Canonical Proset.inl.
Canonical Proset.inr.
Canonical Proset.merge.
Canonical Proset.fst.
Canonical Proset.snd.
Canonical Proset.existT.
Canonical Proset.sigT_map.
Canonical Proset.exp.
Canonical Proset.cat.
Canonical Proset.botCat.
Canonical Proset.topCat.
Canonical Proset.coprodCat.
Canonical Proset.prodCat.
Canonical Proset.scoprodCat.
Canonical Proset.sprodCat.
Canonical Proset.expCat.
Canonical Proset.cartCat.
Canonical Proset.CCC.

Canonical Proset.Forget.
Canonical Proset.Discrete.
Canonical Proset.discreteCU.
Canonical Proset.Indiscrete.
Canonical Proset.indiscreteU.
Canonical Proset.category.
Canonical Proset.hom_func.
Canonical Proset.Cat.
Canonical Proset.Conn.
Canonical Proset.ConnU.
Canonical Proset.ConnCU.

Module Poset.

Module obj.

Structure mixin_of (P: Proset.obj) := Mixin {
  le_antisym (x y: P): x <= y -> y <= x -> x = y;
}.

Lemma mixin_eq {P} (c d: mixin_of P): c = d.
Proof. apply proof_irrelevance. Qed.

Structure class_of T := Class {
  base: Proset.obj.mixin_of T;
  mixin: mixin_of (Proset.obj.Pack T base);
}.

Lemma class_eq {T} (c d: class_of T): c = d <-> forall x y, Proset.obj.le T (base T c) x y <-> Proset.obj.le T (base T d) x y.
Proof.
  rewrite <- Proset.obj.mixin_eq.
  split.
  now intros [].
  destruct c as [c Hc], d as [d Hd]; simpl.
  intros H.
  subst d.
  f_equal; apply proof_irrelevance.
Qed.

Structure type := Pack { sort: Type; _: class_of sort }.

Section ClassDef.
Local Coercion base: class_of >-> Proset.obj.mixin_of.
Local Coercion mixin: class_of >-> mixin_of.
Local Coercion sort: type >-> Sortclass.

Variable (T: type).
Definition class := match T return class_of T with Pack _ c => c end.

Let xT := match T with Pack T _ => T end.
Notation xclass := (class: class_of xT).

Definition Proset := Proset.obj.Pack T xclass.

End ClassDef.

Module Exports.
Coercion base: class_of >-> Proset.obj.mixin_of.
Coercion mixin: class_of >-> mixin_of.
Coercion sort: type >-> Sortclass.
Coercion Proset: type >-> Proset.obj.
Canonical Proset.

Definition le_antisym {T: type}: forall x y: T, x <= y -> y <= x -> x = y := le_antisym T (class T).
Instance le_partialorder {T: type}: PartialOrder eq (@le T).
Proof.
  intros x y.
  change (x = y <-> x <= y /\ y <= x).
  split.
  now intros [].
  intros [].
  now apply le_antisym.
Qed.

End Exports.
End obj.
Export obj.Exports.
Notation obj := obj.type.

Definition cat_mixin := Category.Mixin obj Proset.hom
  (@id Proset) (@comp Proset) (@comp_assoc Proset) (@comp_id_l Proset) (@comp_id_r Proset).
Canonical cat := Category.Pack obj cat_mixin.

Program Definition dual_mixin (P: obj) := obj.Mixin (Proset.dual P) _.
Next Obligation.
  now apply le_antisym.
Qed.
Definition dual_class (P: obj) := obj.Class P (Proset.dual_mixin P) (dual_mixin P).
Definition dual (P: obj) := obj.Pack P (dual_class P).

Program Definition Dual: Functor cat cat := {|
  fobj := dual;
  fmap := @Proset.dual_map;
|}.

Lemma dual_invol (P: obj): dual (dual P) = P.
Proof.
  destruct P as [T c].
  unfold dual; simpl.
  f_equal.
  now apply obj.class_eq.
Qed.

Program Definition empty_mixin := obj.Mixin Proset.empty _.
Next Obligation. easy. Qed.
Definition empty_class := obj.Class Empty_set Proset.empty_mixin empty_mixin.
Canonical empty := obj.Pack Empty_set empty_class.

Program Definition botCat_mixin := BotCategory.Mixin cat empty
  (fun P => {|
    Proset.map := Empty_set_rect (fun _ => P);
  |}) _.
Next Obligation.
  contradiction.
Qed.
Next Obligation.
  now apply Proset.hom_eq.
Qed.
Canonical botCat := BotCategory.Pack cat botCat_mixin.

Program Definition unit_mixin := obj.Mixin Proset.unit _.
Next Obligation.
  now destruct x, y.
Qed.
Definition unit_class := obj.Class unit Proset.unit_mixin unit_mixin.
Canonical unit := obj.Pack unit unit_class.

Program Definition topCat_mixin := TopCategory.Mixin cat unit
  (fun P => {|
    Proset.map _ := tt;
  |}) _.
Next Obligation.
  reflexivity.
Qed.
Next Obligation.
  apply Proset.hom_eq; simpl.
  intros x.
  now destruct (f x).
Qed.
Canonical topCat := TopCategory.Pack cat topCat_mixin.

Program Definition sum_mixin (A B: obj) := obj.Mixin (Proset.sum A B) _.
Next Obligation.
  destruct x as [x|x], y as [y|y]; simpl in *.
  2, 3: contradiction.
  all: f_equal.
  all: now apply le_antisym.
Qed.
Definition sum_class (A B: obj) := obj.Class (A + B) (Proset.sum_mixin A B) (sum_mixin A B).
Canonical sum (A B: obj) := obj.Pack (A + B) (sum_class A B).

Program Definition coprodCat_mixin := CoprodCategory.Mixin cat sum
  (@Proset.merge) (@Proset.inl) (@Proset.inr) _.
Next Obligation.
  split.
  + intros H.
    subst h.
    split.
    all: now apply Proset.hom_eq.
  + intros [].
    subst f g.
    apply Proset.hom_eq; simpl.
    now intros [].
Qed.
Canonical coprodCat := CoprodCategory.Pack cat coprodCat_mixin.

Program Definition prod_mixin (A B: obj) := obj.Mixin (Proset.prod A B) _.
Next Obligation.
  f_equal.
  all: apply le_antisym.
  1, 3: apply H.
  all: apply H0.
Qed.
Definition prod_class (A B: obj) := obj.Class (A * B) (Proset.prod_mixin A B) (prod_mixin A B).
Canonical prod (A B: obj) := obj.Pack (A * B) (prod_class A B).

Program Definition prodCat_mixin := ProdCategory.Mixin cat prod
  (fun X Y Z f g => {|
    Proset.map x := (f x, g x);
  |}) (@Proset.fst) (@Proset.snd) _.
Next Obligation.
  now split; simpl; apply Proset.monotone.
Qed.
Next Obligation.
  split.
  + intros H.
    subst h.
    split.
    all: now apply Proset.hom_eq.
  + intros [].
    subst f g.
    apply Proset.hom_eq; simpl.
    intros x.
    now destruct (h x).
Qed.
Canonical prodCat := ProdCategory.Pack cat prodCat_mixin.

Program Definition sigT_mixin {I} (F: I -> obj) := obj.Mixin (Proset.sigT F) _.
Next Obligation.
  destruct H as [e H1], H0 as [e1 H2]; simpl in *.
  subst y.
  rewrite (proof_irrelevance _ e1 eq_refl) in H2; clear e1.
  f_equal.
  now apply le_antisym.
Qed.
Definition sigT_class {I} (F: I -> obj) := obj.Class (sigT F) (Proset.sigT_mixin F) (sigT_mixin F).
Canonical sigT {I} (F: I -> obj) := obj.Pack (sigT F) (sigT_class F).

Program Definition scoprodCat_mixin := SCoprodCategory.Mixin cat (@sigT) (@Proset.sigT_map) (@Proset.existT) _.
Next Obligation.
  split.
  + intros H.
    subst g.
    intros i.
    now apply Proset.hom_eq.
  + intros H.
    apply functional_extensionality_dep in H.
    subst f.
    apply Proset.hom_eq; simpl.
    now intros [i x].
Qed.
Canonical scoprodCat := SCoprodCategory.Pack cat scoprodCat_mixin.

Program Definition Prod_mixin {I} (F: I -> obj) := obj.Mixin (Proset.Prod F) _.
Next Obligation.
  extensionality i.
  now apply le_antisym.
Qed.
Definition Prod_class {I} (F: I -> obj) := obj.Class (forall i, F i) (Proset.Prod_mixin F) (Prod_mixin F).
Definition Prod {I} (F: I -> obj) := obj.Pack (forall i, F i) (Prod_class F).

Program Definition sprodCat_mixin := SProdCategory.Mixin cat
  (@Prod)
  (fun I T F f => {|
    Proset.map x i := f i x;
  |})
  (fun I F i => {|
    Proset.map x := x i;
  |}) _.
Next Obligation.
  intros i.
  now apply Proset.monotone.
Qed.
Next Obligation.
  split.
  + intros H.
    subst g.
    intros i.
    now apply Proset.hom_eq.
  + intros H.
    apply functional_extensionality_dep in H.
    subst f.
    now apply Proset.hom_eq.
Qed.
Canonical sprodCat := SProdCategory.Pack cat sprodCat_mixin.

Definition cartCat_class := CartCategory.Class cat topCat_mixin prodCat_mixin.
Canonical cartCat := CartCategory.Pack cat cartCat_class.

Program Definition exp_mixin (T S: obj) := obj.Mixin (Proset.exp T S) _.
Next Obligation.
  apply Proset.hom_eq.
  intros i.
  now apply le_antisym.
Qed.
Definition exp_class (T S: obj) := obj.Class (Proset.hom S T) (Proset.exp_mixin T S) (exp_mixin T S).
Canonical exp (T S: obj) := obj.Pack (Proset.hom S T) (exp_class T S).

Program Definition expCat_mixin := ExpCategory.Mixin prodCat
  exp
  (fun T S => {|
    Proset.map p := fst p (snd p);
  |})
  (fun T S P => {|
    Proset.map (f: (P × S) ~> T) := {|
      Proset.map x := {|
        Proset.map y := f (x, y);
      |};
    |};
  |}) _.
Next Obligation.
  destruct H as [Hh Hs]; simpl in *.
  now rewrite Hs.
Qed.
Next Obligation.
  now apply Proset.monotone.
Qed.
Next Obligation.
  intros z; simpl.
  now apply Proset.monotone.
Qed.
Next Obligation.
  intros f z; simpl.
  apply H.
Qed.
Next Obligation.
  split.
  + intros H.
    subst f.
    apply Proset.hom_eq; simpl.
    intros a.
    now apply Proset.hom_eq; simpl.
  + intros H.
    subst g.
    apply Proset.hom_eq; simpl.
    now intros [].
Qed.
Definition expCat_class := ExpCategory.Class cat prodCat_mixin expCat_mixin.
Canonical expCat := ExpCategory.Pack cat expCat_class.

Definition CCC_class := CCC.Class cat cartCat_class expCat_mixin.
Canonical CCC := CCC.Pack cat CCC_class.

Definition forget_map {S T: obj} (f: S ~> T): obj.Proset S ~> T := f.

Program Canonical Forget: Functor cat Proset := {|
  fobj := obj.Proset;
  fmap := @forget_map;
|}.

Structure strict (P: Proset) := {
  sclass: P -> Prop;
  sclass_correct: exists x, forall y, sclass y <-> x ≃ y;
}.

Arguments sclass {P} s p.
Arguments sclass_correct {P} s.
Coercion sclass: strict >-> Funclass.

Program Definition strictObj {P: Proset} (x: P) := {|
  sclass y := x ≃ y;
|}.
Next Obligation.
  now exists x.
Qed.

Lemma strict_eq {P: Proset} (X Y: strict P): X = Y <-> forall x, X x <-> Y x.
Proof.
  split.
  now intros [].
  destruct X as [X HX], Y as [Y HY]; simpl.
  intros H.
  enough (X = Y); [subst Y|].
  f_equal; apply proof_irrelevance.
  extensionality x.
  apply propositional_extensionality.
  apply H.
Qed.

Lemma strictObj_eq {P: Proset} (X: strict P) (x: P): X = strictObj x <-> X x.
Proof.
  split.
  + intros HX.
    now subst X; simpl.
  + intros Hx.
    apply strict_eq.
    intros z; simpl.
    destruct (sclass_correct X) as [y Hy].
    rewrite Hy.
    f_equiv.
    now apply Hy.
Qed.

Lemma strictObj_surj {P: Proset} (X: strict P): exists x, strictObj x = X.
Proof.
  destruct (sclass_correct X) as [x Hx].
  exists x.
  symmetry.
  now apply strictObj_eq, Hx.
Qed.

Program Definition strict_pro_mixin (P: Proset) := Proset.obj.Mixin (strict P) (fun X Y => forall x y, X x -> Y y -> x <= y) _.
Next Obligation.
  split.
  + intros X x y Hx Hy.
    destruct (sclass_correct X) as [z Hz].
    rewrite <- (proj1 (Hz x) Hx).
    rewrite <- (proj1 (Hz y) Hy).
    reflexivity.
  + intros X Y Z H1 H2 x z Hx Hz.
    destruct (sclass_correct Y) as [y Hy].
    specialize (Hy y).
    apply proj2 in Hy.
    specialize (Hy (reflexivity y)).
    transitivity y.
    now apply H1.
    now apply H2.
Qed.
Canonical strict_pro (P: Proset) := Proset.obj.Pack (strict P) (strict_pro_mixin P).

Program Definition strict_po_mixin (P: Proset) := obj.Mixin (strict_pro P) _.
Next Obligation.
  rename x into X, y into Y.
  destruct (strictObj_surj X) as [x HX].
  destruct (strictObj_surj Y) as [y HY].
  subst X Y.
  apply strictObj_eq, Proset.iso_alt.
  split.
  now apply H; simpl.
  now apply H0; simpl.
Qed.
Definition strict_po_class (P: Proset) := obj.Class (strict P) (strict_pro_mixin P) (strict_po_mixin P).
Canonical strict_po (P: Proset) := obj.Pack (strict P) (strict_po_class P).

Program Definition strict_map {S T: Proset} (f: S ~> T) (X: strict S): strict T := {|
  sclass y := forall x, X x -> f x ≃ y;
|}.
Next Obligation.
  destruct (strictObj_surj X) as [x HX].
  subst X.
  exists (f x).
  intros y.
  split.
  + intros Hy.
    now apply Hy; simpl.
  + intros Hy z Hz; simpl in Hz.
    rewrite <- Hy.
    now apply Proset.map_iso.
Qed.

Lemma strict_map_obj {S T: Proset} (f: S ~> T) (x: S): strict_map f (strictObj x) = strictObj (f x).
Proof.
  apply strictObj_eq; simpl.
  intros y H.
  now apply Proset.map_iso.
Qed.

Program Canonical Strict_map {S T: Proset} (f: S ~> T): strict_pro S ~> strict_pro T := {|
  Proset.map := strict_map f;
|}.
Next Obligation.
  rename x into X, y into Y.
  destruct (strictObj_surj X) as [x HX].
  destruct (strictObj_surj Y) as [y HY].
  subst X Y.
  rewrite !strict_map_obj.
  intros a b H1 H2; simpl in *.
  rewrite <- H1, <- H2.
  now apply Proset.monotone, H; simpl.
Qed.

Program Canonical Strict := {|
  fobj := strict_po;
  fmap := @Strict_map;
|}.
Next Obligation.
  apply Proset.hom_eq.
  intros X.
  destruct (strictObj_surj X) as [x HX].
  subst X.
  apply strict_map_obj.
Qed.
Next Obligation.
  apply Proset.hom_eq.
  intros X.
  destruct (strictObj_surj X) as [x HX].
  subst X; simpl.
  now rewrite !strict_map_obj.
Qed.

Program Canonical strict_unit (P: Proset): P ~> strict_pro P := {|
  Proset.map := strictObj;
|}.
Next Obligation.
  intros a b H1 H2; simpl in *.
  now rewrite <- H1, <- H2.
Qed.

Program Canonical strictU: id Proset ~> Forget ∘ Strict := {|
  transform := strict_unit;
|}.
Next Obligation.
  apply Proset.hom_eq; simpl.
  intros z.
  symmetry.
  apply strict_map_obj.
Qed.

Lemma strict_inhabited {P: Proset} (X: strict P): inhabited P.
Proof. now destruct (strictObj_surj X) as [x Hx]. Qed.

Definition strictStrong {P: obj} (X: strict P): P :=
  epsilon (strict_inhabited X) X.

Lemma strictStrong_spec {P: obj} (X: strict P): X (strictStrong X).
Proof.
  unfold strictStrong.
  apply epsilon_spec.
  destruct (strictObj_surj X) as [x Hx].
  subst X.
  now exists x; simpl.
Qed.

Lemma strictStrong_obj {P: obj} (x: P): strictStrong (strictObj x) = x.
Proof.
  apply le_antisym.
  all: apply Proset.iso_alt.
  2: symmetry.
  all: apply (strictStrong_spec (strictObj x)).
Qed.

Program Canonical strict_counit (P: obj): strict_pro P ~> P := {|
  Proset.map := strictStrong;
|}.
Next Obligation.
  rename x into X, y into Y.
  destruct (strictObj_surj X) as [x HX].
  destruct (strictObj_surj Y) as [y HY].
  subst X Y.
  rewrite !strictStrong_obj.
  now apply H; simpl.
Qed.

Program Canonical strictCU: Strict ∘ Forget ~> id cat := {|
  transform := strict_counit;
|}.
Next Obligation.
  apply Proset.hom_eq.
  intros X; simpl.
  destruct (strictObj_surj X) as [z HX].
  subst X.
  rewrite strict_map_obj, !strictStrong_obj.
  reflexivity.
Qed.

Lemma strict_adjoint: adjoint_by Strict Forget strictU strictCU.
Proof.
  apply adjoint_by_alt.
  split.
  + intros P.
    apply Proset.hom_eq.
    intros X; simpl in *.
    destruct (strictObj_surj X) as [x HX].
    subst X.
    now rewrite strict_map_obj, strictStrong_obj.
  + intros P.
    apply Proset.hom_eq; simpl.
    apply strictStrong_obj.
Qed.

End Poset.

Export Poset.obj.Exports.
Notation Poset := Poset.cat.
Canonical Poset.empty.
Canonical Poset.unit.
Canonical Poset.sum.
Canonical Poset.prod.
Canonical Poset.sigT.
Canonical Poset.exp.
Canonical Poset.cat.
Canonical Poset.botCat.
Canonical Poset.topCat.
Canonical Poset.coprodCat.
Canonical Poset.prodCat.
Canonical Poset.scoprodCat.
Canonical Poset.sprodCat.
Canonical Poset.expCat.
Canonical Poset.cartCat.
Canonical Poset.CCC.

Canonical Poset.Forget.

Definition is_proset (C: Category) :=
  forall (x y: C) (f g: x ~> y), f = g.

Definition is_directed (C: Category) :=
  forall x y: C, x ~> y -> y ~> x -> x = y.

Definition is_poset (C: Category) :=
  is_proset C /\ is_directed C.

Lemma Proset_correct (P: Proset): is_proset P.
Proof.
  intros x y f g.
  apply Proset.chom_eq.
Qed.

Lemma Poset_correct (P: Poset.obj): is_poset P.
Proof.
  split.
  apply Proset_correct.
  intros x y f g.
  now apply le_antisym.
Qed.

Lemma proset_ex (C: Category): is_proset C -> Proset.category (Proset.Conn C) ≃ C.
Proof.
  intros H.
  assert (inhabited (forall (x y: C) (f: @hom (Proset.Conn C) x y), x ~> y)).
    apply inhabit_forall.
    intros x.
    apply inhabit_forall.
    intros y.
    apply inhabit_forall.
    intros f.
    exact f.
  destruct H0 as [F].
  constructor.
  unshelve eexists.
  1: exists (fun x: Proset.Conn C => x: C) F.
  3: exists (Proset.ConnU C).
  3, 4: fun_eq x y f.
  all: intros.
  3: apply Proset.chom_eq.
  all: apply H.
Qed.

Lemma dual_proset (P: Proset): co P = Proset.dual P.
Proof.
  unfold co, Proset.dual, Proset.category; simpl.
  f_equal.
  apply cat_mixin_eq; simpl.
  repeat split.
  intros x e.
  apply proof_irrelevance.
  intros x y z f g e1 e2 e3.
  apply proof_irrelevance.
Qed.

Lemma dual_poset (P: Poset): co P = Poset.dual P.
Proof. apply dual_proset. Qed.
