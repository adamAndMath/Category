Require Export Structure.Product.

Definition is_exp {C: ProdCategory} (t s p: C) (e: p × s ~> t) :=
  forall x (f: x × s ~> t), exists! g: x ~> p, e ∘ (g (×) id s) = f.

Definition is_exp_obj {C: ProdCategory} (t s p: C) :=
  exists e, is_exp t s p e.

Definition ex_exp {C: ProdCategory} (t s: C) :=
  exists p, is_exp_obj t s p.

Instance is_exp_obj_iso (C: ProdCategory): Proper (isomorphic C ==> isomorphic C ==> isomorphic C ==> iff) is_exp_obj.
Proof.
  enough (Proper (isomorphic C ==> isomorphic C ==> isomorphic C ==> impl) is_exp_obj).
  now split; apply H.
  intros a x [i] b y [j] p q [k] [e H].
  exists (i ∘ e ∘ (k⁻¹ (×) j⁻¹)).
  intros z f'.
  assert (exists f, i ∘ f ∘ (id z (×) j⁻¹) = f').
    exists (i⁻¹ ∘ f' ∘ (id z (×) j)).
    rewrite !comp_assoc, <- comp_assoc.
    rewrite fprod_comp.
    rewrite !inv_r, !comp_id_l.
    rewrite fprod_id.
    apply comp_id_r.
  destruct H0 as [f].
  subst f'.
  specialize (H z f).
  destruct H as [g [H u]].
  subst f.
  exists (k ∘ g); split.
  rewrite <- !comp_assoc.
  do 2 f_equal.
  rewrite !fprod_comp.
  f_equal.
  rewrite comp_assoc, comp_id_r.
  rewrite inv_l.
  apply comp_id_l.
  rewrite comp_id_l.
  apply comp_id_r.
  intros h H.
  rewrite <- !comp_assoc in H.
  apply iso_monic in H.
  rewrite !fprod_comp, !comp_id_r, comp_id_l in H.
  apply (iso_monic k⁻¹).
  rewrite comp_assoc.
  rewrite inv_l, comp_id_l.
  apply u.
  rewrite <- (inv_l j).
  rewrite <- (comp_id_r (k⁻¹ ∘ h)).
  rewrite <- (comp_id_r g).
  rewrite <- !fprod_comp.
  rewrite !comp_assoc.
  now f_equal.
Qed.

Instance ex_exp_iso (C: ProdCategory): Proper (isomorphic C ==> isomorphic C ==> iff) ex_exp.
Proof.
  intros a x H1 b y H2.
  unfold ex_exp.
  f_equiv; intros z.
  now f_equiv.
Qed.

Lemma exp_obj_euniqueness {C: ProdCategory} (a b: C): euniqueness (is_exp_obj a b).
Proof.
  intros P Q [p Hp] [q Hq].
  destruct (Hq P p) as [f [Hf _]].
  destruct (Hp Q q) as [g [Hg _]].
  constructor.
  exists f, g.
  all: symmetry.
  + specialize (Hp P p).
    destruct Hp as [p' [Hp H]].
    transitivity p'.
    symmetry.
    all: apply H.
    rewrite fprod_id.
    apply comp_id_r.
    rewrite <- (comp_id_l (id b)).
    rewrite <- fprod_comp, comp_assoc.
    now rewrite Hg.
  + specialize (Hq Q q).
    destruct Hq as [q' [Hq H]].
    transitivity q'.
    symmetry.
    all: apply H.
    rewrite fprod_id.
    apply comp_id_r.
    rewrite <- (comp_id_l (id b)).
    rewrite <- fprod_comp, comp_assoc.
    now rewrite Hf.
Qed.

Lemma ex_exp_eunique {C: ProdCategory} (a b: C): ex_exp a b <-> exists!! p, is_exp_obj a b p.
Proof.
  rewrite <- eunique_existence.
  split.
  + intros H.
    split.
    now apply is_exp_obj_iso.
    split.
    exact H.
    apply exp_obj_euniqueness.
  + intros [_ [H _]].
    exact H.
Qed.

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

Lemma eval_is_exp (a b: C): is_exp a b (a ^ b) (eval a b).
Proof.
  intros z f.
  exists (transpose f); split.
  apply eval_transpose.
  intros g.
  apply transpose_ump.
Qed.

Lemma exp_is_exp_obj (a b: C): is_exp_obj a b (a ^ b).
Proof.
  exists (eval a b).
  apply eval_is_exp.
Qed.

End Exponential.

Infix "^" := exp.

Lemma exp_correct (C: ProdCategory): inhabited (ExpCategory.mixin_of C) <-> (forall a b: C, ex_exp a b).
Proof.
  split.
  + intros [[E e t H]] a b.
    exists (E a b), (e a b).
    intros z f.
    exists (t a b z f); split.
    now apply H.
    intros g.
    apply H.
  + intros H.
    generalize (fun a => ex_forall _ (H a)).
    clear H; intros H.
    apply ex_forall in H.
    destruct H as [E H].
    generalize (fun a => ex_forall _ (H a)).
    clear H; intros H.
    apply ex_forall in H.
    destruct H as [e H].
    generalize (fun a b z => ex_forall _ (H a b z)).
    clear H; intros H.
    generalize (fun a b => ex_forall _ (H a b)).
    clear H; intros H.
    generalize (fun a => ex_forall _ (H a)).
    clear H; intros H.
    apply ex_forall in H.
    destruct H as [t H].
    constructor.
    exists E e t.
    intros a b c f g.
    specialize (H a b c f).
    destruct H as [H u].
    split.
    intros Hh.
    now apply u.
    intros Hg.
    now subst g.
Qed.
