Require Export Structure.

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

End Slice.

Notation Slice := Slice.cat.
Infix "/" := Slice.
