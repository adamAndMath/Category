Require Export Structure.Terminal.
Require Export Structure.Product.

Module CartCategory.

Section ClassDef.

Structure class_of (C: Category) := Class {
  base: TopCategory.class_of C;
  mixin: ProdCategory.class_of C;
}.
Local Coercion base: class_of >-> TopCategory.class_of.
Local Coercion mixin: class_of >-> ProdCategory.class_of.

Structure type := Pack { sort: Category; _: class_of sort }.
Local Coercion sort: type >-> Category.

Variable (C: type).
Definition class := match C return class_of C with Pack _ c => c end.

Let xC := match C with Pack C _ => C end.
Notation xclass := (class: class_of xC).

Definition TopCategory := TopCategory.Pack C xclass.
Definition ProdCategory := ProdCategory.Pack C xclass.

End ClassDef.

Module Exports.

Coercion base: class_of >-> TopCategory.class_of.
Coercion mixin: class_of >-> ProdCategory.class_of.
Coercion sort: type >-> Category.
Coercion TopCategory: type >-> TopCategory.type.
Canonical TopCategory.
Coercion ProdCategory: type >-> ProdCategory.type.
Canonical ProdCategory.
Notation CartCategory := type.

End Exports.

End CartCategory.

Export CartCategory.Exports.

Section Cartisian.
Context {C: CartCategory}.

Section prod_unitor_l.
Context (x: C).

Definition prod_unitor_l_to: x × 1 ~> x := π₁.
Definition prod_unitor_l_from: x ~> x × 1 := ⟨id x, to_one⟩.

Lemma prod_unitor_l_inv_l: prod_unitor_l_from ∘ prod_unitor_l_to = id (x × 1).
Proof.
  unfold prod_unitor_l_to, prod_unitor_l_from.
  rewrite fork_comp, <- fork_id.
  f_equal.
  apply comp_id_l.
  transitivity (@to_one C (x × 1)).
  symmetry.
  all: apply to_one_unique.
Qed.

Lemma prod_unitor_l_inv_r: prod_unitor_l_to ∘ prod_unitor_l_from = id x.
Proof.
  unfold prod_unitor_l_to, prod_unitor_l_from.
  apply pi1_fork.
Qed.

Definition prod_unitor_l: x × 1 <~> x :=
  Isomorphism.Pack prod_unitor_l_to (Isomorphism.Mixin _ _ _ prod_unitor_l_to prod_unitor_l_from prod_unitor_l_inv_l prod_unitor_l_inv_r).

Lemma prod_1_l: x × 1 ≃ x.
Proof.
  constructor.
  exact prod_unitor_l.
Qed.
End prod_unitor_l.

Section prod_unitor_r.
Context (x: C).

Definition prod_unitor_r_to: (1: C) × x ~> x := π₂.
Definition prod_unitor_r_from: x ~> (1: C) × x := ⟨@to_one C _, id x⟩.

Lemma prod_unitor_r_inv_l: prod_unitor_r_from ∘ prod_unitor_r_to = id ((1: C) × x).
Proof.
  unfold prod_unitor_r_to, prod_unitor_r_from.
  rewrite fork_comp, <- fork_id.
  f_equal.
  transitivity (@to_one C ((1: C) × x)).
  symmetry.
  1, 2: apply to_one_unique.
  apply comp_id_l.
Qed.

Lemma prod_unitor_r_inv_r: prod_unitor_r_to ∘ prod_unitor_r_from = id x.
Proof.
  unfold prod_unitor_r_to, prod_unitor_r_from.
  apply pi2_fork.
Qed.

Definition prod_unitor_r: (1: C) × x <~> x :=
  Isomorphism.Pack prod_unitor_r_to (Isomorphism.Mixin _ _ _ prod_unitor_r_to prod_unitor_r_from prod_unitor_r_inv_l prod_unitor_r_inv_r).

Lemma prod_1_r: (1: C) × x ≃ x.
Proof.
  constructor.
  exact prod_unitor_r.
Qed.
End prod_unitor_r.

End Cartisian.
