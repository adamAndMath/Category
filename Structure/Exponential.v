Require Export Structure.Product.

Module ExpCategory.

Structure mixin_of (C: ProdCategory) := Mixin {
  exp: C -> C -> C;
  eval (t s: C): exp t s × s ~> t;
  transpose (t s x: C): x × s ~> t -> x ~> exp t s;
  transpose_ump (t s x: C) (f: x × s ~> t) (g: x ~> exp t s): eval t s ∘ (g (×) id s) = f <-> transpose t s x f = g;
}.

Section ClassDef.

Structure class_of (C: Category) := Class {
  base: ProdCategory.mixin_of C;
  mixin: mixin_of (ProdCategory.Pack C base);
}.
Local Coercion base: class_of >-> ProdCategory.mixin_of.

Structure type := Pack { sort: Category; _: class_of sort }.
Local Coercion sort: type >-> Category.

Variable (C: type).
Definition class := match C return class_of C with Pack _ c => c end.

Let xC := match C with Pack C _ => C end.
Notation xclass := (class: class_of xC).

Definition ProdCategory := ProdCategory.Pack C xclass.

End ClassDef.

Module Exports.

Coercion base: class_of >-> ProdCategory.mixin_of.
Coercion mixin: class_of >-> mixin_of.
Coercion sort: type >-> Category.
Coercion ProdCategory: type >-> ProdCategory.type.
Canonical ProdCategory.
Notation ExpCategory := type.

End Exports.

End ExpCategory.

Export ExpCategory.Exports.

Section Exponential.
Context {C: ExpCategory}.

Definition exp: C -> C -> C := ExpCategory.exp C (ExpCategory.class C).
Definition eval: forall t s: C, exp t s × s ~> t := ExpCategory.eval C (ExpCategory.class C).
Definition transpose: forall {t s x: C}, x × s ~> t -> x ~> exp t s := ExpCategory.transpose C (ExpCategory.class C).

Infix "^" := exp.

Lemma transpose_ump {t s x: C} (f: x × s ~> t) (g: x ~> t ^ s): eval t s ∘ (g (×) id s) = f <-> transpose f = g.
Proof. apply ExpCategory.transpose_ump. Qed.

Lemma eval_transpose {t s x: C} (f: x × s ~> t): eval t s ∘ (transpose f (×) id s) = f.
Proof.
  now apply transpose_ump.
Qed.

Definition transpose_inv {t s x: C} (f: x ~> t ^ s): x × s ~> t :=
  eval t s ∘ (f (×) id s).

Lemma transpose_inv_l {t s x: C} (f: x × s ~> t): transpose_inv (transpose f) = f.
Proof.
  apply eval_transpose.
Qed.

Lemma transpose_inv_r {t s x: C} (f: x ~> t ^ s): transpose (transpose_inv f) = f.
Proof.
  now apply transpose_ump.
Qed.

Lemma transpose_inj {t s x: C} (f g: x × s ~> t): transpose f = transpose g <-> f = g.
Proof.
  split; intros H.
  setoid_rewrite <- transpose_inv_l.
  all: now f_equal.
Qed.

Lemma transpose_inv_inj {t s x: C} (f g: x ~> t ^ s): transpose_inv f = transpose_inv g <-> f = g.
Proof.
  rewrite <- transpose_inj.
  f_equiv.
  all: apply transpose_inv_r.
Qed.

Definition comp_l {x y z: C} (f: y ~> z): x ^ z ~> x ^ y :=
  transpose (eval x z ∘ (id (x ^ z) (×) f)).

Definition comp_r {x y z: C} (f: x ~> y): x ^ z ~> y ^ z :=
  transpose (f ∘ eval x z).

Lemma comp_l_id (t s: C): comp_l (id s) = id (t ^ s).
Proof. apply transpose_inv_r. Qed.

Lemma comp_r_id (t s: C): comp_r (id t) = id (t ^ s).
Proof.
  unfold comp_r.
  rewrite comp_id_l, <- (comp_id_r (eval t s)).
  rewrite <- fprod_id.
  apply transpose_inv_r.
Qed.

Lemma comp_l_comp {t x y z: C} (f: y ~> z) (g: x ~> y): @comp_l t _ _ g ∘ comp_l f = comp_l (f ∘ g).
Proof.
  unfold comp_l.
  apply transpose_inv_inj.
  rewrite transpose_inv_l.
  unfold transpose_inv.
  rewrite <- (comp_id_l (id x)).
  rewrite <- fprod_comp, comp_assoc.
  rewrite eval_transpose.
  rewrite <- comp_assoc, fprod_comp.
  rewrite comp_id_l, comp_id_r.
  rewrite <- (comp_id_l g), <- (comp_id_r (transpose _)).
  rewrite <- fprod_comp, comp_assoc.
  rewrite eval_transpose.
  rewrite <- comp_assoc, fprod_comp.
  now rewrite !comp_id_l.
Qed.

Lemma comp_r_comp {x y z s: C} (f: y ~> z) (g: x ~> y): @comp_r _ _ s f ∘ comp_r g = comp_r (f ∘ g).
Proof.
  unfold comp_r.
  apply transpose_inv_inj.
  rewrite transpose_inv_l.
  unfold transpose_inv.
  rewrite <- (comp_id_l (id s)).
  rewrite <- fprod_comp, comp_assoc.
  rewrite eval_transpose.
  rewrite <- !comp_assoc.
  f_equal.
  apply eval_transpose.
Qed.

Section comp_l_iso.
Context {x y z: C} (f: y <~> z).

Lemma comp_l_inv_l: comp_l f⁻¹ ∘ comp_l f = id (x ^ z).
Proof.
  rewrite comp_l_comp, <- comp_l_id.
  f_equal.
  apply inv_r.
Qed.

Lemma comp_l_inv_r: comp_l f ∘ comp_l f⁻¹ = id (x ^ y).
Proof.
  rewrite comp_l_comp, <- comp_l_id.
  f_equal.
  apply inv_l.
Qed.

Canonical comp_l_iso: x ^ z <~> x ^ y :=
  Isomorphism.Pack (comp_l f) (Isomorphism.Mixin _ _ _ (comp_l f) (comp_l f⁻¹) comp_l_inv_l comp_l_inv_r).

End comp_l_iso.

Section comp_r_iso.
Context {x y z: C} (f: x <~> y).

Lemma comp_r_inv_l: comp_r f⁻¹ ∘ comp_r f = id (x ^ z).
Proof.
  rewrite comp_r_comp, <- comp_r_id.
  f_equal.
  apply inv_l.
Qed.

Lemma comp_r_inv_r: comp_r f ∘ comp_r f⁻¹ = id (y ^ z).
Proof.
  rewrite comp_r_comp, <- comp_r_id.
  f_equal.
  apply inv_r.
Qed.

Canonical comp_r_iso: x ^ z <~> y ^ z :=
  Isomorphism.Pack (comp_r f) (Isomorphism.Mixin _ _ _ (comp_r f) (comp_r f⁻¹) comp_r_inv_l comp_r_inv_r).

End comp_r_iso.

Global Instance exp_iso: Proper (isomorphic C ==> isomorphic C ==> isomorphic C) exp.
Proof.
  intros x x' Hx y y' Hy.
  transitivity (x' ^ y).
  1: clear y' Hy; destruct Hx as [i].
  2: clear x Hx; rename x' into x; destruct Hy as [i].
  all: constructor.
  now apply comp_r_iso.
  now apply comp_l_iso, inv.
Qed.

End Exponential.

Infix "^" := exp.