Require Export Base.

Module Slice.

Section category.
Context (C: Category) (c: C).

Structure obj := Obj {
  dom: C;
  oarr: dom ~> c;
}.

Structure hom (f g: obj) := Morph {
  arr: dom f ~> dom g;
  comm: oarr g ∘ arr = oarr f;
}.

Local Arguments arr {f g} _.
Local Arguments comm {f g} _.
Local Coercion arr: hom >-> Categories.hom.

Lemma obj_eq {f g: obj}: f = g <-> dom f = dom g /\ (forall e: dom f = dom g, oarr f = oarr g ∘ eq_iso e).
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

Lemma hom_eq {f g: obj} (a b: hom f g): a = b <-> arr a = arr b.
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

Definition id (f: obj): hom f f := {|
  arr := id (dom f);
  comm := comp_id_r (oarr f)
|}.

Definition comp {f g h: obj} (a: hom g h) (b: hom f g): hom f h := {|
  arr := a ∘ b;
  comm := eq_trans (comp_assoc _ _ _) (eq_trans (f_equal (fun f => f ∘ _) (comm a)) (comm b))
|}.

Lemma comp_assoc (f g h i: obj) (F: hom h i) (G: hom g h) (H: hom f g): comp F (comp G H) = comp (comp F G) H.
Proof.
  apply hom_eq; simpl.
  apply comp_assoc.
Qed.

Lemma comp_id_l (f g: obj) (a: hom f g): comp (id g) a = a.
Proof.
  apply hom_eq; simpl.
  apply comp_id_l.
Qed.

Lemma comp_id_r (f g: obj) (a: hom f g): comp a (id f) = a.
Proof.
  apply hom_eq; simpl.
  apply comp_id_r.
Qed.

Definition cat_mixin: Category.mixin_of obj :=
  Category.Mixin obj hom id (@comp) comp_assoc comp_id_l comp_id_r.

Canonical cat: Category :=
  Category.Pack obj cat_mixin.

End category.

Arguments dom {C c} _.
Arguments oarr {C c} _.
Arguments arr {C c f g} _.
Arguments comm {C c f g} _.

Definition Dom (C: Category) (c: C): cat C c ~> C := {|
  fobj := dom;
  fmap := @arr C c;
  fmap_id _ := eq_refl;
  fmap_comp _ _ _ _ _ := eq_refl;
|}.

End Slice.

Canonical Slice.cat.
Notation Slice := Slice.cat.
Infix "/" := Slice.

Definition Coslice (C: Category) (c: C) := co (co C / c).
Infix "\" := Coslice (at level 40, left associativity).
