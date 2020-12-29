Require Export Structure.Cartisian.
Require Export Structure.Exponential.

Module CCC.

Section ClassDef.

Structure class_of (C: Category) := Class {
  base: CartCategory.class_of C;
  mixin: ExpCategory.mixin_of (CartCategory.Pack C base);
}.
Local Coercion base: class_of >-> CartCategory.class_of.
Local Coercion mixin: class_of >-> ExpCategory.mixin_of.

Structure type := Pack { sort: Category; _: class_of sort }.
Local Coercion sort: type >-> Category.

Variable (C: type).
Definition class := match C return class_of C with Pack _ c => c end.

Let xC := match C with Pack C _ => C end.
Notation xclass := (class: class_of xC).

Definition TopCategory := TopCategory.Pack C xclass.
Definition ProdCategory := ProdCategory.Pack C xclass.
Definition CartCategory := CartCategory.Pack C xclass.
Definition ExpCategory := ExpCategory.Pack C (ExpCategory.Class _ xclass xclass).

End ClassDef.

Module Exports.

Coercion base: class_of >-> CartCategory.class_of.
Coercion mixin: class_of >-> ExpCategory.mixin_of.
Coercion sort: type >-> Category.
Coercion TopCategory: type >-> TopCategory.type.
Canonical TopCategory.
Coercion ProdCategory: type >-> ProdCategory.type.
Canonical ProdCategory.
Coercion CartCategory: type >-> CartCategory.type.
Canonical CartCategory.
Coercion ExpCategory: type >-> ExpCategory.type.
Canonical ExpCategory.
Notation CCC := type.

End Exports.

End CCC.

Export CCC.Exports.

Section CartisianClosed.
Context {C: CCC}.

Section exp_1.
Context (c: C).

Definition expc1_to: c ^ 1 ~> c :=
  eval c 1 ∘ ⟨id (c ^ 1), !⟩.

Definition expc1_from: c ~> c ^ 1 :=
  transpose π₁.

Lemma expc1_inv_l: expc1_from ∘ expc1_to = id (c ^ 1).
Proof.
  unfold expc1_to, expc1_from.
  apply transpose_inv_inj.
  unfold transpose_inv.
  etransitivity.
  do 2 apply f_equal.
  symmetry.
  apply comp_id_l.
  setoid_rewrite fprod_comp.
  rewrite comp_assoc.
  setoid_rewrite eval_transpose.
  unfold fprod.
  rewrite <- comp_assoc, fork_comp.
  rewrite !comp_id_l.
  rewrite pi1_fork.
  do 2 f_equal.
  apply to_one_eq.
Qed.

Lemma expc1_inv_r: expc1_to ∘ expc1_from = id c.
Proof.
  unfold expc1_to, expc1_from.
  rewrite <- comp_assoc.
  rewrite fork_comp.
  rewrite comp_id_l.
  apply (iso_epic (prod_unitor_l c)).
  rewrite comp_id_l.
  simpl.
  unfold prod_unitor_l_to.
  rewrite <- comp_assoc, fork_comp.
  rewrite (to_one_eq _ (id 1 ∘ @π₂ _ c 1)).
  apply (eval_transpose (@π₁ _ c 1)).
Qed.

Definition expc1: c ^ 1 <~> c :=
  Isomorphism.Pack expc1_to (Isomorphism.Mixin _ _ _ expc1_to expc1_from expc1_inv_l expc1_inv_r).

Lemma exp_1_r: c ^ 1 ≃ c.
Proof.
  constructor.
  exact expc1.
Qed.

End exp_1.

End CartisianClosed.
