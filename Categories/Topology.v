Require Export Structure.

Module Topology.

Module obj.

Structure mixin_of T := Mixin {
  open: (T -> Prop) -> Prop;
  open_all: open (fun _ => True);
  open_union {I} (F: I -> T -> Prop): (forall i, open (F i)) -> open (fun x => exists i, F i x);
  open_and (A B: T -> Prop): open A -> open B -> open (fun x => A x /\ B x);
}.

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

Module Open.

Structure obj (T: obj) := {
  class: T -> Prop;
  class_open: open T class;
}.

Arguments class {T} o t.
Arguments class_open {T} o.
Coercion class: obj >-> Funclass.

Definition hom {T} (X Y: obj T) := forall x, X x -> Y x.

Lemma hom_eq {T} {X Y: obj T} (f g: hom X Y): f = g.
Proof. apply proof_irrelevance. Qed.

Program Definition cat_mixin T := Category.Mixin (obj T) hom
  (fun X x H => H)
  (fun X Y Z f g x H => f x (g x H))
  _ _ _.

Canonical cat T := Category.Pack (obj T) (cat_mixin T).

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

End Open.

Notation Open := Open.cat.

End Topology.

Export Topology.obj.Exports.
Coercion Topology.map: Topology.hom >-> Funclass.
Canonical Topology.sig.
Canonical Topology.Open.cat.
Canonical Topology.Open.prod.
Canonical Topology.Open.scoprod.
Coercion Topology.Open.class: Topology.Open.obj >-> Funclass.
Canonical Topology.cat.
Notation Topology := Topology.cat.
