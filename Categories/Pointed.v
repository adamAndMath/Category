Require Export Structure.

Module Pointed.
Section category.
Context {C: TopCategory}.

Structure obj := Obj {
  carrier: C;
  element: 1 ~> carrier;
}.

Local Coercion carrier: obj >-> Category.obj.

Structure hom (X Y: obj) := Hom {
  arr: X ~> Y;
  comm: arr ∘ element X = element Y;
}.

Global Arguments Hom {X Y} arr comm.
Global Arguments arr {X Y} _.
Global Arguments comm {X Y} _.
Local Coercion arr: hom >-> Categories.hom.

Lemma obj_eq (X Y: obj): X = Y <-> carrier X = Y /\ forall e: carrier X = Y, eq_iso e ∘ element X = element Y.
Proof.
  split.
  + intros H.
    subst Y.
    split.
    reflexivity.
    intros e.
    rewrite eq_iso_refl; clear e.
    apply comp_id_l.
  + destruct X as [X x], Y as [Y y].
    simpl.
    intros [Hc He].
    subst Y.
    specialize (He eq_refl).
    simpl in He.
    rewrite comp_id_l in He.
    now f_equal.
Qed.

Lemma hom_eq {X Y: obj} (f g: hom X Y): f = g <-> arr f = g.
Proof.
  split.
  intros H.
  now subst g.
  destruct f as [f Hf], g as [g Hg].
  simpl.
  intros H.
  subst g.
  f_equal.
  apply proof_irrelevance.
Qed.

Let id (X: obj): hom X X := {|
  arr := id X;
  comm := comp_id_l (element X);
|}.

Program Let comp {X Y Z: obj} (f: hom Y Z) (g: hom X Y): hom X Z := {|
  arr := f ∘ g;
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite comm.
  apply comm.
Qed.

Lemma comp_assoc {X Y Z V: obj} (f: hom Z V) (g: hom Y Z) (h: hom X Y): comp f (comp g h) = comp (comp f g) h.
Proof.
  apply hom_eq; simpl.
  apply comp_assoc.
Qed.

Lemma comp_id_l {X Y: obj} (f: hom X Y): comp (id Y) f = f.
Proof.
  apply hom_eq; simpl.
  apply comp_id_l.
Qed.

Lemma comp_id_r {X Y: obj} (f: hom X Y): comp f (id X) = f.
Proof.
  apply hom_eq; simpl.
  apply comp_id_r.
Qed.

Definition cat_mixin: Category.mixin_of obj :=
  Category.Mixin obj hom id (@comp) (@comp_assoc) (@comp_id_l) (@comp_id_r).

Definition cat := Category.Pack obj cat_mixin.

End category.

Arguments obj C: clear implicits.
Arguments cat_mixin C: clear implicits.
Arguments cat C: clear implicits.

Program Definition forget {C: TopCategory}: Functor (cat C) C := {|
  fobj := carrier;
  fmap := @arr C;
|}.

End Pointed.

Notation Pointed := Pointed.cat.
