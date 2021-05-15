Require Export Structure.

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

Definition is_basis {T} (F: (T -> Prop) -> Prop) :=
  (forall x, exists P, F P /\ P x) /\
  (forall L R x, F L -> F R -> L x -> R x -> exists P, F P /\ P x /\ (forall x, P x -> L x /\ R x)).

Program Definition basis_mixin {T} (F: (T -> Prop) -> Prop) (H: is_basis F) := obj.Mixin T (fun P => exists G: (T -> Prop) -> Prop, (forall P, G P -> F P) /\ (fun x => exists P, G P /\ P x) = P) _ _ _.
Next Obligation.
  exists F; split.
  easy.
  extensionality x.
  apply propositional_extensionality.
  split; intros _.
  exact I.
  apply H.
Qed.
Next Obligation.
  apply ex_forall in H0.
  destruct H0 as [G HG].
  exists (fun P => exists i, G i P); split.
  intros P [i HP].
  now apply (HG i).
  extensionality x.
  apply propositional_extensionality.
  split.
  + intros [P [[i HP] Hx]].
    exists i.
    rewrite <- (proj2 (HG i)).
    now exists P.
  + intros [i Hx].
    rewrite <- (proj2 (HG i)) in Hx.
    destruct Hx as [P [HP Hx]].
    exists P; split.
    now exists i.
    exact Hx.
Qed.
Next Obligation.
  rename H0 into L, H4 into HL, H1 into R, H2 into HR.
  exists (fun P => F P /\ exists l r, L l /\ R r /\ forall x, P x -> l x /\ r x); split.
  now intros P [HP _].
  extensionality x.
  apply propositional_extensionality.
  split.
  + intros [P [[HP [l [r [Hl [Hr Hp]]]]] Hx]].
    specialize (Hp x Hx).
    split.
    now exists l.
    now exists r.
  + intros [[l [Hl lx]] [r [Hr rx]]].
    apply proj2 in H.
    specialize (H l r x (HL l Hl) (HR r Hr) lx rx) as [P [HP [Px Hx]]].
    exists P; repeat split.
    exact HP.
    now exists l, r.
    exact Px.
Qed.

Lemma open_basis (T: obj): is_basis (open T).
Proof.
  split.
  + intros x.
    exists (fun _ => True); split.
    apply open_all.
    exact I.
  + intros L R x HL HR Lx Rx.
    exists (fun x => L x /\ R x); split.
    now apply open_and.
    easy.
Qed.

Lemma open_basis_eq (T: obj): basis_mixin (open T) (open_basis T) = obj.class T.
Proof.
  apply obj.mixin_eq.
  intros P.
  split.
  + intros [F [HF HP]].
    subst P.
    apply open_union.
    intros P.
    destruct (classic (F P)) as [HP | HP].
    specialize (HF P HP).
    revert HF.
    change (?P -> ?Q) with (impl P Q).
    f_equiv.
    extensionality x.
    now apply propositional_extensionality.
    now apply open_never'.
  + intros HP.
    exists (eq P); split.
    now intros _ [].
    extensionality x.
    apply propositional_extensionality.
    split.
    now intros [_ [[] Hx]].
    intros Hx.
    now exists P.
Qed.

Lemma basis_open {T} (F: (T -> Prop) -> Prop) (HF: is_basis F) (P: T -> Prop): F P -> obj.open T (basis_mixin F HF) P.
Proof.
  intros HP.
  exists (eq P); split.
  now intros _ [].
  extensionality x.
  apply propositional_extensionality.
  split.
  now intros [_ [[] Hx]].
  intros Hx.
  now exists P.
Qed.

Lemma basis_continue {S: obj} {T} (F: (T -> Prop) -> Prop) (HF: is_basis F) (f: S -> T): (forall P: T -> Prop, obj.open T (basis_mixin F HF) P -> open S (fun x => P (f x))) <-> (forall P: T -> Prop, F P -> open S (fun x => P (f x))).
Proof.
  split; intros H P.
  + intros HP.
    apply H.
    exists (eq P); split.
    now intros _ [].
    extensionality x.
    apply propositional_extensionality.
    split.
    now intros [_ [[] Hx]].
    intros Hx.
    now exists P.
  + intros [G [HG HP]].
    subst P.
    enough (forall P, (exists Q, G Q /\ (fun x => Q (f x)) = P) -> open S P).
    apply open_union' in H0.
    revert H0.
    change (?P -> ?Q) with (impl P Q).
    f_equiv.
    extensionality x.
    apply propositional_extensionality.
    split.
    - intros [_ [[P [HP []]] Hx]].
      now exists P.
    - intros [P [HP Hx]].
      exists (fun x => P (f x)); split.
      now exists P.
      exact Hx.
    - intros _ [P [HP []]].
      apply H, HG, HP.
Qed.

Program Definition sig_mixin {T: obj} (P: T -> Prop) := obj.Mixin (sig P)
  (fun S => exists Q, open T Q /\ S = (fun x => Q (proj1_sig x)))
  _ _ _.
Next Obligation.
  exists (fun _ => True); split.
  apply open_all.
  reflexivity.
Qed.
Next Obligation.
  apply ex_forall in H.
  destruct H as [G H].
  exists (fun x => exists i, G i x); split.
  apply open_union.
  intros i.
  apply H.
  extensionality x.
  apply propositional_extensionality.
  f_equiv.
  intros i.
  now rewrite (proj2 (H i)).
Qed.
Next Obligation.
  rename H into L, H3 into HL, H0 into R, H1 into HR.
  exists (fun x => L x /\ R x); split.
  now apply open_and.
  reflexivity.
Qed.

Canonical sig {T: obj} (P: T -> Prop) := obj.Pack (sig P) (sig_mixin P).

Program Canonical proj1_sig {T: obj} {P: T -> Prop} := {|
  map := @proj1_sig T P;
|}.
Next Obligation.
  now exists P0; split.
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
  destruct H as [Q [HQ HP]].
  subst P.
  now exists Q.
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

Program Definition prod_mixin (T U: obj) := @basis_mixin (T * U) (fun P => exists L R, (fun p => L (fst p) /\ R (snd p)) = P /\ open T L /\ open U R) _.
Next Obligation.
  split.
  + intros [x y].
    exists (fun _ => True); repeat split.
    exists (fun _ => True), (fun _ => True); split.
    extensionality p.
    now apply propositional_extensionality.
    split; apply open_all.
  + intros _ _ [x y] [L1 [R1 [[] [HL1 HR1]]]] [L2 [R2 [[] [HL2 HR2]]]] [Lx Ly] [Rx Ry]; simpl in *.
    exists (fun p => (L1 (fst p) /\ L2 (fst p)) /\ R1 (snd p) /\ R2 (snd p)); split.
    exists (fun x => L1 x /\ L2 x), (fun y => R1 y /\ R2 y); split.
    reflexivity.
    now split; apply open_and.
    easy.
Qed.
Canonical prod (T U: obj) := obj.Pack (T * U) (prod_mixin T U).

Program Canonical fst {T U: obj} := {|
  map := @fst T U;
|}.
Next Obligation.
  apply basis_open.
  exists P, (fun _ => True); split.
  extensionality p.
  now apply propositional_extensionality.
  split.
  exact H.
  apply open_all.
Qed.

Program Canonical snd {T U: obj} := {|
  map := @snd T U;
|}.
Next Obligation.
  apply basis_open.
  exists (fun _ => True), P; split.
  extensionality p.
  now apply propositional_extensionality.
  split.
  apply open_all.
  exact H.
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
  intros _ [P [Q [[] [HP HQ]]]].
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

Program Definition Prod_mixin {I} (F: I -> obj) := @basis_mixin (forall i, F i) (fun P => exists l: list ((forall i, F i) -> Prop), (fun f => forall P, List.In P l -> P f) = P /\ (forall P, List.In P l -> exists i (Q: F i -> Prop), open (F i) Q /\ (fun f => Q (f i)) = P)) _.
Next Obligation.
  split.
  + intros f.
    exists (fun _ => True); split.
    exists nil; split.
    extensionality g.
    now apply propositional_extensionality.
    intros _ [].
    easy.
  + intros _ _ f [l [[] Hl]] [r [[] Hr]] lf rf.
    exists (fun f => forall P, List.In P (l ++ r) -> P f); split.
    exists (l ++ r)%list; split.
    reflexivity.
    intros P HP.
    apply List.in_app_or in HP.
    destruct HP as [HP | HP].
    now apply Hl.
    now apply Hr.
    split.
    intros P HP.
    apply List.in_app_or in HP.
    destruct HP as [HP | HP].
    now apply lf.
    now apply rf.
    intros g Hg; split.
    all: intros P HP.
    all: apply Hg, List.in_or_app.
    all: now [> left | right].
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
  intros _ [l [[] Hl]].
  induction l; simpl.
  now apply open_all'.
  specialize (IHl (fun P HP => Hl P (or_intror HP))).
  specialize (Hl a (or_introl eq_refl)) as [i [Q [HQ Ha]]].
  subst a.
  apply (continue (f i)) in HQ.
  generalize (open_and T _ _ HQ IHl).
  change (?P -> ?Q) with (impl P Q).
  f_equiv.
  extensionality x.
  apply propositional_extensionality.
  split.
  + intros [Qx lx] P [HP | HP].
    now subst P.
    now apply lx.
  + intros H; split.
    apply (H (fun f => Q (f i))).
    now left.
    intros P HP.
    apply H.
    now right.
Qed.
Next Obligation.
  apply basis_open.
  exists ((fun f => P (f i)) :: nil)%list; split.
  extensionality f.
  apply propositional_extensionality.
  split.
  intros HP.
  apply HP.
  now left.
  now intros HP _ [[]|[]].
  intros _ [[]|[]].
  now exists i, P.
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
Notation Topology := Topology.cat.
