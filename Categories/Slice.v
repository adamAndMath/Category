Require Export Base.

Module Slice.

Structure obj (C: Category) (c: C) := Obj {
  dom: C;
  arr: dom ~> c;
}.

Arguments dom {C c} o.
Arguments arr {C c} o.

Structure hom {C: Category} {c: C} (f g: obj C c) := Hom {
  map: dom f ~> dom g;
  comm: arr g ∘ map = arr f;
}.

Arguments Hom {C c f g} map comm.
Arguments map {C c f g} _.
Arguments comm {C c f g} _.
Coercion map: hom >-> Categories.hom.

Lemma obj_eq {C: Category} {c: C} {f g: obj C c}: f = g <-> dom f = dom g /\ (forall e: dom f = dom g, arr f = arr g ∘ eq_iso e).
Proof.
  split.
  + intros H.
    subst g.
    repeat split.
    intros e.
    rewrite eq_iso_refl.
    symmetry.
    apply comp_id_r.
  + destruct f as [x f], g as [x' g].
    simpl.
    intros [Hx H].
    subst x'.
    f_equal.
    rewrite <- comp_id_r.
    exact (H eq_refl).
Qed.

Lemma hom_eq {C: Category} {c: C} {f g: obj C c} (a b: hom f g): a = b <-> map a = map b.
Proof.
  split.
  intros H.
  now subst b.
  destruct a as [a Ha], b as [b Hb].
  simpl.
  intros H.
  subst b.
  f_equal.
  apply proof_irrelevance.
Qed.

Program Definition cat_mixin (C: Category) (c: C) := Category.Mixin (obj C c) hom
  (fun f => {|
    map := id (dom f);
    comm := comp_id_r (arr f);
  |})
  (fun f g h a b => {|
    map := a ∘ b;
    comm := eq_trans (comp_assoc _ _ _) (eq_trans (f_equal (fun f => f ∘ _) (comm a)) (comm b));
  |})
  _ _ _.
Next Obligation.
  apply hom_eq; simpl.
  apply comp_assoc.
Qed.
Next Obligation.
  apply hom_eq; simpl.
  apply comp_id_l.
Qed.
Next Obligation.
  apply hom_eq; simpl.
  apply comp_id_r.
Qed.

Canonical cat (C: Category) (c: C): Category :=
  Category.Pack (obj C c) (cat_mixin C c).

Program Canonical Dom (C: Category) (c: C): cat C c ~> C := {|
  fobj := dom;
  fmap := @map C c;
|}.

End Slice.

Canonical Slice.cat.
Canonical Slice.Dom.
Coercion Slice.map: Slice.hom >-> hom.
Notation Slice := Slice.cat.
Infix "/" := Slice.

Module Coslice.

Structure obj (C: Category) (c: C) := Obj {
  cod: C;
  arr: c ~> cod;
}.

Arguments cod {C c} o.
Arguments arr {C c} o.

Structure hom {C: Category} {c: C} (f g: obj C c) := Hom {
  map: cod f ~> cod g;
  comm: map ∘ arr f = arr g;
}.

Arguments Hom {C c f g} map comm.
Arguments map {C c f g} _.
Arguments comm {C c f g} _.
Coercion map: hom >-> Categories.hom.

Lemma obj_eq {C: Category} {c: C} {f g: obj C c}: f = g <-> cod f = cod g /\ (forall e: cod f = cod g, eq_iso e ∘ arr f = arr g).
Proof.
  split.
  + intros H.
    subst g.
    repeat split.
    intros e.
    rewrite eq_iso_refl.
    apply comp_id_l.
  + destruct f as [x f], g as [x' g].
    simpl.
    intros [Hx H].
    subst x'.
    f_equal.
    rewrite <- (comp_id_l f).
    exact (H eq_refl).
Qed.

Lemma hom_eq {C: Category} {c: C} {f g: obj C c} (a b: hom f g): a = b <-> map a = map b.
Proof.
  split.
  intros H.
  now subst b.
  destruct a as [a Ha], b as [b Hb].
  simpl.
  intros H.
  subst b.
  f_equal.
  apply proof_irrelevance.
Qed.

Program Definition cat_mixin (C: Category) (c: C) := Category.Mixin (obj C c) hom
  (fun f => {|
    map := id (cod f);
    comm := comp_id_l (arr f);
  |})
  (fun f g h a b => {|
    map := a ∘ b;
    comm := eq_trans (eq_sym (comp_assoc _ _ _)) (eq_trans (f_equal (fun f => _ ∘ f) (comm b)) (comm a));
  |})
  _ _ _.
Next Obligation.
  apply hom_eq; simpl.
  apply comp_assoc.
Qed.
Next Obligation.
  apply hom_eq; simpl.
  apply comp_id_l.
Qed.
Next Obligation.
  apply hom_eq; simpl.
  apply comp_id_r.
Qed.

Canonical cat (C: Category) (c: C): Category :=
  Category.Pack (obj C c) (cat_mixin C c).

Program Canonical Cod (C: Category) (c: C): cat C c ~> C := {|
  fobj := cod;
  fmap := @map C c;
|}.

End Coslice.

Canonical Coslice.cat.
Canonical Coslice.Cod.
Coercion Coslice.map: Coslice.hom >-> hom.
Notation Coslice := Coslice.cat.
Infix "\" := Coslice (at level 40, left associativity).
