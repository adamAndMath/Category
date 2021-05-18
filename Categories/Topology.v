Require Export Structure.
Require Export Categories.Typ.

Module Topology.

Module obj.

Structure mixin_of T := Mixin {
  open: (T -> Prop) -> Prop;
  open_all: open (fun _ => True);
  open_union {I} (F: I -> T -> Prop): (forall i, open (F i)) -> open (fun x => exists i, F i x);
  open_and (A B: T -> Prop): open A -> open B -> open (fun x => A x /\ B x);
}.

Lemma mixin_eq {T} (c d: mixin_of T): c = d <-> (forall P, open T c P <-> open T d P).
Proof.
  split.
  now intros [].
  destruct c as [c c1 c2 c3], d as [d d1 d2 d3]; simpl.
  intros H.
  enough (c = d); [subst d|].
  f_equal; apply proof_irrelevance.
  extensionality P.
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

Definition open (T: type): (T -> Prop) -> Prop := @open T (class T).
Definition open_all (T: type): open T (fun _ => True) := @open_all T (class T).
Definition open_union (T: type): forall {I} (F: I -> T -> Prop), (forall i, open T (F i)) -> open T (fun x => exists i, F i x) := @open_union T (class T).
Definition open_and (T: type): forall (A B: T -> Prop), open T A -> open T B -> open T (fun x => A x /\ B x) := @open_and T (class T).

Lemma open_all' (T: type) (P: T -> Prop): (forall x, P x) -> open T P.
Proof.
  intros H.
  replace P with (fun _: T => True).
  apply open_all.
  extensionality x.
  now apply propositional_extensionality.
Qed.

Lemma open_never' (T: type) (P: T -> Prop): (forall x, ~P x) -> open T P.
Proof.
  intros H.
  replace P with (fun x: T => exists i: False, (fun _ _ => True) i x).
  now apply open_union.
  extensionality x.
  apply propositional_extensionality.
  split.
  intros [[] _].
  intros Hx.
  now specialize (H x).
Qed.

Lemma open_never (T: type): open T (fun _ => False).
Proof. now apply open_never'. Qed.

Lemma open_or (T: type) (A B: T -> Prop): open T A -> open T B -> open T (fun x => A x \/ B x).
Proof.
  intros HA HB.
  cut (open T (fun x => exists b, (fun b: bool => if b then A else B) b x)).
  change (?P -> ?Q) with (impl P Q).
  f_equiv.
  extensionality x.
  apply propositional_extensionality.
  split.
  + intros [[] Hx].
    all: now [> left | right].
  + intros [Hx | Hx].
    now exists true.
    now exists false.
  + apply open_union.
    now intros [].
Qed.

Lemma open_filter (T: type) (P: Prop) (A: T -> Prop): (P -> open T A) -> open T (fun x => P /\ A x).
Proof.
  intros HA.
  destruct (classic P).
  specialize (HA H).
  revert HA.
  change (?P -> ?Q) with (impl P Q).
  f_equiv.
  extensionality x.
  now apply propositional_extensionality.
  now apply open_never'.
Qed.

Lemma open_union' (T: type) (F: (T -> Prop) -> Prop): (forall P, F P -> open T P) -> open T (fun x => exists P, F P /\ P x).
Proof.
  intros H.
  specialize (fun P => H (proj1_sig P) (proj2_sig P)).
  apply open_union in H.
  revert H.
  change (?P -> ?Q) with (impl P Q).
  f_equiv.
  extensionality x.
  apply propositional_extensionality.
  split.
  + intros [[P HP] Hx].
    now exists P.
  + intros [P [HP Hx]].
    now exists (exist _ P HP).
Qed.

Instance open_iff (T: type): Proper (pointwise_relation T iff ==> iff) (open T).
Proof.
  intros P Q H.
  f_equiv.
  extensionality x.
  now apply propositional_extensionality.
Qed.

End Exports.
End obj.
Export obj.Exports.
Notation obj := obj.type.

Structure hom (X Y: obj) := Hom {
  map: X -> Y;
  continue (P: Y -> Prop): open Y P -> open X (fun x => P (map x));
}.

Arguments map {X Y} h x.
Arguments continue {X Y} h P H.

Coercion map: hom >-> Funclass.

Lemma hom_eq {X Y: obj} (f g: hom X Y): f = g <-> forall x, f x = g x.
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
  (fun X => {|
    map x := x;
    continue P H := H;
  |})
  (fun X Y Z f g => {|
    map x := f (g x);
    continue P H := continue g _ (continue f P H);
  |})
  _ _ _.
Next Obligation.
  now destruct f.
Qed.
Next Obligation.
  now destruct f.
Qed.

Canonical cat := Category.Pack obj cat_mixin.

Class Basis {I T} (F: I -> T -> Prop) :=
  basis: (forall x, exists i, F i x) /\
  (forall i j x, F i x -> F j x -> exists k, F k x /\ (forall x, F k x -> F i x /\ F j x)).

Program Definition basis_mixin {I T} (F: I -> T -> Prop) (H: Basis F) := obj.Mixin T (fun P => exists G: I -> Prop, (fun x => exists i, G i /\ F i x) = P) _ _ _.
Next Obligation.
  exists (fun _ => True).
  extensionality x.
  apply propositional_extensionality.
  split; intros _.
  constructor.
  destruct (proj1 H x) as [i Hi].
  now exists i.
Qed.
Next Obligation.
  rename I0 into J.
  apply ex_forall in H0.
  destruct H0 as [G HG].
  apply functional_extensionality_dep in HG.
  subst F0.
  exists (fun i => exists j, G j i).
  extensionality x.
  apply propositional_extensionality.
  split.
  + intros [i [[j Hj] Hi]].
    now exists j, i.
  + intros [j [i [Hj Hi]]].
    exists i; split.
    now exists j.
    exact Hi.
Qed.
Next Obligation.
  rename H0 into L, H1 into R.
  exists (fun i => exists l r, (L l /\ R r) /\ forall x, F i x -> F l x /\ F r x).
  extensionality x.
  apply propositional_extensionality.
  split.
  + intros [i [[l [r [[Hl Hr] Hi]]] Hx]].
    apply Hi in Hx.
    split.
    now exists l.
    now exists r.
  + intros [[l [Hl H1]] [r [Hr H2]]].
    destruct (proj2 H l r x H1 H2) as [i [Hx Hi]].
    exists i; split.
    now exists l, r.
    exact Hx.
Qed.

Lemma basis_open {I T} (F: I -> T -> Prop) (HF: Basis F) (P: T -> Prop): (exists i, forall x, F i x <-> P x) -> obj.open T (basis_mixin F HF) P.
Proof.
  intros [i Hi].
  exists (eq i).
  extensionality x.
  apply propositional_extensionality.
  rewrite <- Hi.
  split.
  now intros [_ [[] Hx]].
  intros Hx.
  now exists i.
Qed.

Lemma basis_continue {S: obj} {I T} (F: I -> T -> Prop) (HF: Basis F) (f: S -> T): (forall P: T -> Prop, obj.open T (basis_mixin F HF) P -> open S (fun x => P (f x))) <-> (forall i, open S (fun x => F i (f x))).
Proof.
  split.
  + intros H i.
    apply H, basis_open.
    now exists i.
  + intros H _ [P []].
    apply open_union.
    intros i.
    now apply open_filter.
Qed.

Instance open_basis (T: obj): Basis (fun P x => open T P /\ P x).
Proof.
  split.
  + intros x.
    exists (fun _ => True); split.
    apply open_all.
    exact I.
  + intros L R x [HL Lx] [HR Rx].
    exists (fun x => L x /\ R x); split.
    split.
    now apply open_and.
    all: easy.
Qed.

Lemma open_basis_eq (T: obj): basis_mixin (fun P x => open T P /\ P x) _ = obj.class T.
Proof.
  apply obj.mixin_eq.
  intros P.
  split.
  + revert P.
    apply basis_continue.
    intros i.
    now apply open_filter.
  + intros HP.
    apply basis_open.
    now exists P.
Qed.

Program Definition sig_mixin {T: obj} (P: T -> Prop) := basis_mixin (fun Q (x: sig P) => open T Q /\ Q (proj1_sig x)) _.
Next Obligation.
  split.
  + intros x.
    exists (fun _ => True); split.
    apply open_all.
    exact I.
  + intros L R x Lx Rx.
    exists (fun x => L x /\ R x); split.
    split.
    now apply open_and.
    all: easy.
Qed.

Canonical sig {T: obj} (P: T -> Prop) := obj.Pack (sig P) (sig_mixin P).

Program Canonical proj1_sig {T: obj} {P: T -> Prop} := {|
  map := @proj1_sig T P;
|}.
Next Obligation.
  apply basis_open.
  now exists P0.
Qed.

Module Open.

Structure obj (T: obj) := Obj {
  class: T -> Prop;
  class_open: open T class;
}.

Arguments class {T} o t.
Arguments class_open {T} o.
Coercion class: obj >-> Funclass.

Definition hom {T} (X Y: obj T) := forall x, X x -> Y x.

Lemma obj_eq {T} (X Y: obj T): X = Y <-> forall x, X x <-> Y x.
Proof.
  split.
  now intros [].
  destruct X as [X HX], Y as [Y HY]; simpl.
  intros H.
  enough (X = Y); [subst Y|].
  f_equiv; apply proof_irrelevance.
  extensionality x.
  apply propositional_extensionality.
  apply H.
Qed.

Lemma hom_eq {T} {X Y: obj T} (f g: hom X Y): f = g.
Proof. apply proof_irrelevance. Qed.

Program Definition cat_mixin T := Category.Mixin (obj T) hom
  (fun X x H => H)
  (fun X Y Z f g x H => f x (g x H))
  _ _ _.

Canonical cat T := Category.Pack (obj T) (cat_mixin T).

Program Definition Proj {T} := {|
  fobj (U: cat T) := sig U;
  fmap U V f := {|
    map x := exist _ (proj1_sig x) (f (proj1_sig x) (proj2_sig x));
  |};
|}.
Next Obligation.
  revert P H.
  apply basis_continue.
  intros P; simpl.
  apply basis_open.
  now exists P.
Qed.
Next Obligation.
  apply Topology.hom_eq; simpl.
  now intros [x Hx].
Qed.
Next Obligation.
  now apply Topology.hom_eq.
Qed.

Definition preimg {S T} (f: T ~> S) (X: obj S): obj T := {|
  class x := X (f x);
  class_open := continue f X (class_open X);
|}.

Definition preimg_inc {S T} (f: T ~> S) (X Y: obj S): X ~> Y -> preimg f X ~> preimg f Y.
Proof.
  intros H x.
  exact (H (f x)).
Qed.

Program Canonical Preimg {S T} (f: T ~> S): Functor (cat S) (cat T) := {|
  fobj := preimg f;
  fmap := preimg_inc f;
|}.
Next Obligation.
  apply hom_eq.
Qed.
Next Obligation.
  apply hom_eq.
Qed.

Program Definition img {S T} (f: S ~> T) (X: obj S): obj T := {|
  class y := exists Y, hom (preimg f Y) X /\ Y y;
|}.
Next Obligation.
  apply open_union.
  intros Y.
  destruct (classic (hom (preimg f Y) X)).
  generalize (class_open Y).
  change (?P -> ?Q) with (impl P Q).
  f_equiv.
  extensionality y.
  now apply propositional_extensionality.
  now apply open_never'.
Qed.

Definition img_inc {S T} (f: S ~> T) (X Y: obj S): X ~> Y -> img f X ~> img f Y.
Proof.
  intros H y [Z [HZ Hy]].
  exists Z; split.
  intros z Hz.
  apply H, HZ, Hz.
  exact Hy.
Qed.

Program Canonical Img {S T} (f: S ~> T): Functor (cat S) (cat T) := {|
  fobj := img f;
  fmap := img_inc f;
|}.
Next Obligation.
  apply hom_eq.
Qed.
Next Obligation.
  apply hom_eq.
Qed.

Lemma img_unit {S T} (f: S ~> T) (X: obj T): X ~> Img f (Preimg f X).
Proof.
  intros x Hx.
  exists X; split.
  2: exact Hx.
  intros y Hy.
  exact Hy.
Qed.

Program Canonical imgU {S T} (f: S ~> T): id (cat T) ~> Img f ∘ Preimg f := {|
  transform := img_unit f;
|}.
Next Obligation.
  apply hom_eq.
Qed.

Lemma img_counit {S T} (f: S ~> T) (X: obj S): Preimg f (Img f X) ~> X.
Proof.
  intros x [Y [H Hx]].
  apply H, Hx.
Qed.

Program Canonical imgCU {S T} (f: S ~> T): Preimg f ∘ Img f ~> id (cat S) := {|
  transform := img_counit f;
|}.
Next Obligation.
  apply hom_eq.
Qed.

Lemma img_adjoint_by {S T} (f: S ~> T): adjoint_by (Preimg f) (Img f) (imgU f) (imgCU f).
Proof.
  apply adjoint_by_alt; split.
  all: intros X.
  all: apply hom_eq.
Qed.

Program Definition top_mixin T := TopCategory.Mixin (cat T)
  {|
    class _ := True;
    class_open := open_all T;
  |}
  (fun _ _ _ => I)
  _.
Next Obligation.
  apply hom_eq.
Qed.

Canonical top T := TopCategory.Pack (cat T) (top_mixin T).

Program Definition prod_mixin T := ProdCategory.Mixin (cat T)
  (fun X Y => {|
    class x := X x /\ Y x;
  |})
  (fun X Y Z f g x H => conj (f x H) (g x H))
  (fun X Y x => @proj1 _ _)
  (fun X Y x => @proj2 _ _)
  _.
Next Obligation.
  apply open_and.
  all: apply class_open.
Qed.
Next Obligation.
  repeat split; intros.
  all: apply hom_eq.
Qed.

Canonical prod T := ProdCategory.Pack (cat T) (prod_mixin T).

Lemma preimg_prod {S T} (f: T ~> S) (X Y: obj S): preimg f (X × Y) = preimg f X × preimg f Y.
Proof. now apply obj_eq. Qed.

Lemma img_prod {S T} (f: S ~> T) (X Y: obj S): img f (X × Y) = img f X × img f Y.
Proof.
  apply obj_eq.
  intros x.
  split.
  + intros [Z [HZ Hx]].
    split.
    all: exists Z; split.
    2, 4: exact Hx.
    all: intros z Hz.
    all: apply HZ, Hz.
  + intros [[L [HL Lx]] [R [HR Rx]]].
    exists (L × R); split.
    2: now split.
    intros z Hz; split.
    apply HL, Hz.
    apply HR, Hz.
Qed.

Program Definition coprod_mixin T := CoprodCategory.Mixin (cat T)
  (fun X Y => {|
    class x := X x \/ Y x;
  |})
  (fun X Y Z f g x H =>
    match H with
    | or_introl H => f x H
    | or_intror H => g x H
    end
  )
  (fun X Y x => @or_introl _ _)
  (fun X Y x => @or_intror _ _)
  _.
Next Obligation.
  apply open_or.
  all: apply class_open.
Qed.
Next Obligation.
  repeat split; intros.
  all: apply hom_eq.
Qed.

Canonical coprod T := CoprodCategory.Pack (cat T) (coprod_mixin T).

Program Definition scoprod_mixin T := SCoprodCategory.Mixin (cat T)
  (fun I F => {|
    class x := exists i, F i x;
  |})
  _ _ _.
Next Obligation.
  apply open_union.
  intros i.
  apply class_open.
Qed.
Next Obligation.
  intros x [i H].
  exact (X0 i x H).
Qed.
Next Obligation.
  intros x H; simpl.
  now exists i.
Qed.
Next Obligation.
  split; intros.
  all: apply hom_eq.
Qed.

Canonical scoprod T := SCoprodCategory.Pack (cat T) (scoprod_mixin T).

Lemma preimg_scoprod {I S T} (f: T ~> S) (F: I -> obj S): preimg f (∑ i, F i) = ∑ i, preimg f (F i).
Proof. now apply obj_eq. Qed.

Lemma img_scoprod {I S T} (f: S ~> T) (F: I -> obj S): ∑ i, img f (F i) ~> img f (∑ i, F i).
Proof.
  intros y [i [Y [HY Hy]]].
  exists Y; split.
  2: exact Hy.
  intros x H.
  exists i.
  apply HY, H.
Qed.

End Open.

Notation Open := Open.cat.

Module OpenN.
Import Open.

Structure obj (T: Topology.obj) (x: T) := Obj {
  forget: Open.obj T;
  class_point: forget x;
}.

Arguments forget {T x} o.
Arguments class_point {T x} o.
Coercion forget: obj >-> Open.obj.

Definition hom {T x} (X Y: obj T x) := Open.hom X Y.

Lemma obj_eq {T x} (X Y: obj T x): X = Y <-> forall x, X x <-> Y x.
Proof.
  rewrite <- Open.obj_eq.
  split.
  now intros [].
  destruct X as [X HX], Y as [Y HY]; simpl.
  intros H.
  subst Y.
  f_equiv; apply proof_irrelevance.
Qed.

Lemma hom_eq {T x} {X Y: obj T x} (f g: hom X Y): f = g.
Proof. apply proof_irrelevance. Qed.

Program Definition cat_mixin T x := Category.Mixin (obj T x) hom
  (fun X x H => H)
  (fun X Y Z f g x H => f x (g x H))
  _ _ _.

Canonical cat T x := Category.Pack (obj T x) (cat_mixin T x).

Program Definition top_mixin T x := TopCategory.Mixin (cat T x)
  {|
    forget := 1;
    class_point := I;
  |}
  (fun _ _ _ => I)
  _.
Next Obligation.
  apply hom_eq.
Qed.

Canonical top T x := TopCategory.Pack (cat T x) (top_mixin T x).

Program Definition prod_mixin T x := ProdCategory.Mixin (cat T x)
  (fun X Y => {|
    forget := forget X × Y;
    class_point := conj (class_point X) (class_point Y);
  |})
  (fun X Y Z f g x H => conj (f x H) (g x H))
  (fun X Y x => @proj1 _ _)
  (fun X Y x => @proj2 _ _)
  _.
Next Obligation.
  repeat split; intros.
  all: apply hom_eq.
Qed.

Canonical prod T x := ProdCategory.Pack (cat T x) (prod_mixin T x).

Program Definition coprod_mixin T x := CoprodCategory.Mixin (cat T x)
  (fun X Y => {|
    forget := forget X + Y;
  |})
  (fun X Y Z f g x H =>
    match H with
    | or_introl H => f x H
    | or_intror H => g x H
    end
  )
  (fun X Y x => @or_introl _ _)
  (fun X Y x => @or_intror _ _)
  _.
Next Obligation.
  left.
  apply class_point.
Qed.
Next Obligation.
  repeat split; intros.
  all: apply hom_eq.
Qed.

Canonical coprod T x := CoprodCategory.Pack (cat T x) (coprod_mixin T x).

Definition forget_inc {T x} (X Y: obj T x) (H: hom X Y): Open.hom (forget X) (forget Y) := H.

Program Canonical Forget {T x}: Functor (cat T x) (Open T) := {|
  fobj := @forget T x;
  fmap := forget_inc;
|}.

End OpenN.

Notation OpenN := OpenN.cat.

Program Definition empty_mixin := obj.Mixin Empty_set (fun _ => True) _ _ _.
Canonical empty := obj.Pack Empty_set empty_mixin.

Program Definition botCat_mixin := BotCategory.Mixin cat
  empty
  (fun T => {|
    map := Empty_set_rect (fun _ => T);
    continue P _ := I;
  |})
  _.
Next Obligation.
  now apply hom_eq.
Qed.
Canonical botCat := BotCategory.Pack cat botCat_mixin.

Program Definition unit_mixin := obj.Mixin unit (fun _ => True) _ _ _.
Canonical unit := obj.Pack unit unit_mixin.

Program Definition topCat_mixin := TopCategory.Mixin cat
  unit
  (fun T => {|
    map _ := tt;
  |})
  _.
Next Obligation.
  destruct (classic (P tt)).
  now apply open_all'.
  now apply open_never'.
Qed.
Next Obligation.
  apply hom_eq; simpl.
  intros x.
  now destruct (f x).
Qed.
Canonical topCat := TopCategory.Pack cat topCat_mixin.

Program Definition sum_mixin (T U: obj) := obj.Mixin (T + U) (fun P => open T (fun x => P (inl x)) /\ open U (fun x => P (inr x))) _ _ _.
Next Obligation.
  split; apply open_all.
Qed.
Next Obligation.
  split; apply open_union.
  all: intros i; apply H.
Qed.
Next Obligation.
  now split; apply open_and.
Qed.
Canonical sum (T U: obj) := obj.Pack (T + U) (sum_mixin T U).

Program Canonical inl {T U: obj} := {|
  map := @inl T U;
|}.
Next Obligation.
  apply H.
Qed.

Program Canonical inr {T U: obj} := {|
  map := @inr T U;
|}.
Next Obligation.
  apply H.
Qed.

Program Definition coprodCat_mixin := CoprodCategory.Mixin cat sum
  (fun L R T f g => {|
    map x := match x with Datatypes.inl x => f x | Datatypes.inr x => g x end;
  |})
  (@inl) (@inr)
  _.
Next Obligation.
  now split; apply continue.
Qed.
Next Obligation.
  split.
  + intros H.
    subst h.
    now split; apply hom_eq.
  + intros [].
    subst f g.
    apply hom_eq; simpl.
    now intros [].
Qed.
Canonical coprodCat := CoprodCategory.Pack cat coprodCat_mixin.

Program Definition prod_mixin (T U: obj) := basis_mixin (fun (P: (T -> Prop) * (U -> Prop)) p => (open T (fst P) /\ open U (snd P)) /\ fst P (fst p) /\ snd P (snd p)) _.
Next Obligation.
  split.
  + intros [x y].
    exists (fun _ => True, fun _ => True); split.
    split; apply open_all.
    now split.
  + intros [L1 R1] [L2 R2] p [H1 Hp1] [H2 Hp2]; simpl in *.
    exists (fun x => L1 x /\ L2 x, fun y => R1 y /\ R2 y); split.
    split.
    now split; apply open_and.
    now split.
    clear p Hp1 Hp2.
    now intros p [_]; simpl in *.
Qed.
Canonical prod (T U: obj) := obj.Pack (T * U) (prod_mixin T U).

Program Canonical fst {T U: obj} := {|
  map := @fst T U;
|}.
Next Obligation.
  apply basis_open.
  exists (P, (fun _ => True)); simpl.
  intros p; split.
  easy.
  intros Hp.
  do 2 split.
  exact H.
  apply open_all.
  exact Hp.
  exact I.
Qed.

Program Canonical snd {T U: obj} := {|
  map := @snd T U;
|}.
Next Obligation.
  apply basis_open.
  exists ((fun _ => True), P); simpl.
  intros p; split.
  easy.
  intros Hp.
  do 2 split.
  apply open_all.
  exact H.
  exact I.
  exact Hp.
Qed.

Program Definition prodCat_mixin := ProdCategory.Mixin cat prod
  (fun L R T f g => {|
    map x := (f x, g x);
  |})
  (@fst) (@snd)
  _.
Next Obligation.
  revert P H.
  apply basis_continue.
  intros [P Q]; simpl.
  apply open_filter.
  intros [HP HQ].
  apply open_and.
  all: now apply continue.
Qed.
Next Obligation.
  split.
  + intros H.
    subst h.
    now split; apply hom_eq.
  + intros [].
    subst f g.
    apply hom_eq; simpl.
    intros x.
    now destruct (h x).
Qed.
Canonical prodCat := ProdCategory.Pack cat prodCat_mixin.

Program Definition sigT_mixin {I} (F: I -> obj) := obj.Mixin (sigT F) (fun P => forall i, open (F i) (fun x => P (existT F i x))) _ _ _.
Next Obligation.
  apply open_all.
Qed.
Next Obligation.
  now apply open_union.
Qed.
Next Obligation.
  now apply open_and.
Qed.
Canonical sigT {I} (F: I -> obj) := obj.Pack (sigT F) (sigT_mixin F).

Program Canonical existT {I} (F: I -> obj) (i: I) := {|
  map := existT F i;
|}.

Program Canonical sigT_map {I T F} (f: forall i: I, hom (F i) T) := {|
  map := sigT_rect (fun _ => T) f;
|}.
Next Obligation.
  intros i; simpl.
  now apply continue.
Qed.

Program Definition scoprodCat_mixin := SCoprodCategory.Mixin cat (@sigT)
  (@sigT_map) (@existT) _.
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
    now intros [].
Qed.
Canonical scoprodCat := SCoprodCategory.Pack cat scoprodCat_mixin.

Program Definition Prod_mixin {I} (F: I -> obj) := basis_mixin (fun l (f: forall i, F i) => List.Forall (fun P => (exists i (Q: F i -> Prop), open (F i) Q /\ (fun f => Q (f i)) = P) /\ P f) l) _.
Next Obligation.
  split.
  + intros f.
    now exists nil.
  + intros l r f Hl Hr.
    exists (l ++ r)%list; split.
    now apply List_Forall_app.
    clear f Hl Hr.
    intros f.
    apply List_Forall_app.
Qed.

Definition Prod {I} (F: I -> obj) := obj.Pack (forall i, F i) (Prod_mixin F).

Program Definition sprodCat_mixin := SProdCategory.Mixin cat (@Prod)
  (fun I T F f => {|
    map x i := f i x;
  |})
  (fun I F i => {|
    map f := f i;
  |}) _.
Next Obligation.
  revert P H.
  apply basis_continue.
  intros l.
  setoid_rewrite List_Forall_and.
  apply open_filter.
  intros Hl.
  induction Hl.
  now apply open_all'.
  setoid_rewrite List_Forall_cons.
  apply open_and, IHHl.
  destruct H as [i [Q [HQ Hx]]].
  subst x.
  now apply continue.
Qed.
Next Obligation.
  apply basis_open.
  exists ((fun f => P (f i)) :: nil)%list.
  intros f.
  rewrite List_Forall_cons.
  split.
  now intros [[_ Hi] _].
  intros Hi.
  repeat split; [..|easy].
  now exists i, P.
  exact Hi.
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

Program Definition Pull_mixin {X Y Z: obj} (f: X ~> Z) (g: Y ~> Z) := basis_mixin (fun (P: ((X -> Prop) * (Y -> Prop))) (p: PullTyp f g) => (open X (Datatypes.fst P) /\ open Y (Datatypes.snd P)) /\ Datatypes.fst P (pfst p) /\ Datatypes.snd P (psnd p)) _.
Next Obligation.
  split.
  + intros p.
    exists (fun _ => True, fun _ => True); split.
    split; apply open_all.
    split; exact I.
  + intros [L1 R1] [L2 R2] p [H1 Hp1] [H2 Hp2]; simpl in *.
    exists (fun x => L1 x /\ L2 x, fun y => R1 y /\ R2 y); split.
    split.
    now split; apply open_and.
    now split.
    clear p Hp1 Hp2.
    now intros p [_ [Hp1 Hp2]]; simpl in *.
Qed.
Canonical Pull {X Y Z: obj} (f: X ~> Z) (g: Y ~> Z) := obj.Pack (PullTyp f g) (Pull_mixin f g).

Program Canonical pfst {X Y Z: obj} {f: X ~> Z} {g: Y ~> Z} := {|
  map := @pfst X Y Z f g;
|}.
Next Obligation.
  apply basis_open.
  exists (P, fun _ => True).
  intros p; split; simpl.
  now intros [_ [Hp _]].
  intros Hp; repeat split.
  exact H.
  apply open_all.
  exact Hp.
Qed.

Program Canonical psnd {X Y Z: obj} {f: X ~> Z} {g: Y ~> Z} := {|
  map := @psnd X Y Z f g;
|}.
Next Obligation.
  apply basis_open.
  exists (fun _ => True, P).
  intros p; split; simpl.
  now intros [_ [_ Hp]].
  intros Hp; repeat split.
  apply open_all.
  exact H.
  exact Hp.
Qed.

Program Definition pullCat_mixin := PullCategory.Mixin cat (@Pull)
  (@pfst) (@psnd)
  _
  (fun X Y Z V f g p1 p2 H => {|
    map x := {|
      PullTyp.pfst := p1 x;
      PullTyp.psnd := p2 x;
      PullTyp.comm := f_equal (fun f => map f x) H;
    |};
  |}) _ _ _.
Next Obligation.
  apply hom_eq, PullTyp.comm.
Qed.
Next Obligation.
  revert P H0.
  apply basis_continue.
  intros [L R]; simpl.
  apply open_filter.
  intros [HL HR].
  apply open_and.
  all: now apply continue.
Qed.
Next Obligation.
  now apply hom_eq.
Qed.
Next Obligation.
  now apply hom_eq.
Qed.
Next Obligation.
  apply hom_eq; simpl.
  intros e.
  now apply PullTyp.t_eq.
Qed.

Canonical pullCat := PullCategory.Pack cat pullCat_mixin.

Program Canonical Forget: Functor cat Typ := {|
  fobj := obj.sort;
  fmap := @map;
|}.

Program Definition discrete_mixin T := obj.Mixin T (fun _ => True) _ _ _.
Definition discrete T := obj.Pack T (discrete_mixin T).

Program Definition discrete_map {S T} (f: S -> T): discrete S ~> discrete T := {|
  map := f;
|}.

Program Canonical Discrete: Functor Typ cat := {|
  fobj := discrete;
  fmap := @discrete_map;
|}.

Program Definition discreteU: id Typ ~> Forget ∘ Discrete := {|
  transform T x := x;
|}.

Program Definition discrete_unit (T: obj): discrete T ~> T := {|
  map x := x;
  continue P H := I;
|}.

Program Canonical discreteCU: Discrete ∘ Forget ~> id cat := {|
  transform := discrete_unit;
|}.

Lemma discrete_adjoint: adjoint_by Discrete Forget discreteU discreteCU.
Proof.
  apply adjoint_by_alt.
  split.
  + intros T.
    now apply hom_eq.
  + intros T.
    now extensionality x.
Qed.

Program Definition indiscrete_mixin T := obj.Mixin T (fun P => (fun _ => False) = P \/ (fun _ => True) = P) _ _ _.
Next Obligation.
  destruct (classic (forall i, (fun _ => False) = F i)).
  apply functional_extensionality_dep in H0.
  subst F.
  left.
  extensionality x.
  apply propositional_extensionality.
  split.
  intros [].
  intros [_ []].
  apply not_all_ex_not in H0.
  destruct H0 as [i Hi].
  destruct (H i).
  contradiction.
  right.
  extensionality x.
  apply propositional_extensionality.
  split; intros _.
  exists i.
  now rewrite <- H0.
  constructor.
Qed.
Next Obligation.
  destruct H, H0.
  all: subst A B.
  all: [> left..| right].
  all: extensionality x.
  all: now apply propositional_extensionality.
Qed.
Definition indiscrete T := obj.Pack T (indiscrete_mixin T).

Program Definition indiscrete_map {S T} (f: S -> T): indiscrete S ~> indiscrete T := {|
  map := f;
|}.
Next Obligation.
  destruct H; subst P.
  apply open_never.
  apply open_all.
Qed.

Program Canonical Indiscrete: Functor Typ cat := {|
  fobj := indiscrete;
  fmap := @indiscrete_map;
|}.
Next Obligation.
  now apply hom_eq.
Qed.
Next Obligation.
  now apply hom_eq.
Qed.

Program Definition indiscrete_unit (T: obj): T ~> indiscrete T := {|
  map x := x;
|}.
Next Obligation.
  destruct H; subst P.
  apply open_never.
  apply open_all.
Qed.

Program Canonical indiscreteU: id cat ~> Indiscrete ∘ Forget := {|
  transform := indiscrete_unit;
|}.
Next Obligation.
  now apply hom_eq.
Qed.

Program Definition indiscreteCU: Forget ∘ Indiscrete ~> id Typ := {|
  transform T x := x;
|}.

Lemma indiscrete_adjoint: adjoint_by Forget Indiscrete indiscreteU indiscreteCU.
Proof.
  apply adjoint_by_alt.
  split.
  + intros T.
    now extensionality x.
  + intros T.
    now apply hom_eq.
Qed.

End Topology.

Export Topology.obj.Exports.
Coercion Topology.map: Topology.hom >-> Funclass.
Canonical Topology.Open.Preimg.
Canonical Topology.Open.Img.
Canonical Topology.Open.imgU.
Canonical Topology.Open.imgCU.
Canonical Topology.Open.cat.
Canonical Topology.Open.prod.
Canonical Topology.Open.coprod.
Canonical Topology.Open.scoprod.
Coercion Topology.Open.class: Topology.Open.obj >-> Funclass.
Canonical Topology.OpenN.cat.
Canonical Topology.OpenN.prod.
Canonical Topology.OpenN.coprod.
Canonical Topology.OpenN.Forget.
Coercion Topology.OpenN.forget: Topology.OpenN.obj >-> Topology.Open.obj.
Canonical Topology.sig.
Canonical Topology.empty.
Canonical Topology.unit.
Canonical Topology.sum.
Canonical Topology.prod.
Canonical Topology.inl.
Canonical Topology.inr.
Canonical Topology.fst.
Canonical Topology.snd.
Canonical Topology.sigT.
Canonical Topology.existT.
Canonical Topology.cat.
Canonical Topology.botCat.
Canonical Topology.topCat.
Canonical Topology.coprodCat.
Canonical Topology.prodCat.
Canonical Topology.scoprodCat.
Canonical Topology.sprodCat.
Canonical Topology.Forget.
Canonical Topology.Discrete.
Canonical Topology.discreteCU.
Canonical Topology.Indiscrete.
Canonical Topology.indiscreteU.
Notation Topology := Topology.cat.
