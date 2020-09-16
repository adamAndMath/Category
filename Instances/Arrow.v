Require Export Structure.

Structure arrow (C: Category) := {
  dom: C;
  cod: C;
  arr: dom ~> cod;
}.

Arguments dom {C} _.
Arguments cod {C} _.
Arguments arr {C} _.

Structure arrow_hom {C: Category} (f g: arrow C) := {
  fdom: dom f ~> dom g;
  fcod: cod f ~> cod g;
  arr_comm: fcod ∘ arr f = arr g ∘ fdom;
}.

Arguments fdom {C f g} _.
Arguments fcod {C f g} _.
Arguments arr_comm {C f g} _.

Lemma arrow_hom_eq {C} (f g: arrow C) (F G: arrow_hom f g): F = G <-> fdom F = fdom G /\ fcod F = fcod G.
Proof.
  split.
  intros H.
  now subst G.
  destruct F, G.
  simpl.
  intros [H0 H1].
  subst fdom1 fcod1.
  f_equal.
  apply proof_irrelevance.
Qed.

Definition id_arr {C: Category} (f: arrow C): arrow_hom f f := {|
  fdom := id (dom f);
  fcod := id (cod f);
  arr_comm := eq_trans (comp_id_l (arr f)) (eq_sym (comp_id_r (arr f)));
|}.

Definition comp_arr {C: Category} {f g h: arrow C} (F: arrow_hom g h) (G: arrow_hom f g): arrow_hom f h := {|
  fdom := fdom F ∘ fdom G;
  fcod := fcod F ∘ fcod G;
  arr_comm :=
    eq_trans (eq_trans (eq_trans (eq_trans
      (eq_sym (comp_assoc _ _ _))
      (f_equal _ (arr_comm G)))
      (comp_assoc _ _ _))
      (f_equal (fun f => f ∘ _) (arr_comm F)))
      (eq_sym (comp_assoc _ _ _));
|}.

Lemma comp_arr_assoc {C: Category} (a b c d: arrow C) (f: arrow_hom c d) (g: arrow_hom b c) (h: arrow_hom a b): comp_arr f (comp_arr g h) = comp_arr (comp_arr f g) h.
Proof.
  apply arrow_hom_eq; split; simpl.
  all: apply comp_assoc.
Qed.

Lemma comp_arr_id_l {C: Category} (f g: arrow C) (F: arrow_hom f g): comp_arr (id_arr g) F = F.
Proof.
  apply arrow_hom_eq; split; simpl.
  all: apply comp_id_l.
Qed.

Lemma comp_arr_id_r {C: Category} (f g: arrow C) (F: arrow_hom f g): comp_arr F (id_arr f) = F.
Proof.
  apply arrow_hom_eq; split; simpl.
  all: apply comp_id_r.
Qed.

Definition Arrow_mixin (C: Category): Category.mixin_of (arrow C) :=
  Category.Mixin (arrow C) arrow_hom id_arr (@comp_arr C) comp_arr_assoc comp_arr_id_l comp_arr_id_r.

Canonical Arrow (C: Category): Category :=
  Category.Pack (arrow C) (Arrow_mixin C).

Definition Dom (C: Category): Arrow C ~> C := {|
  fobj := dom;
  fmap f g := fdom;
  fmap_id f := eq_refl;
  fmap_comp _ _ _ F G := eq_refl;
|}.

Definition Cod (C: Category): Arrow C ~> C := {|
  fobj := cod;
  fmap f g := fcod;
  fmap_id f := eq_refl;
  fmap_comp _ _ _ F G := eq_refl;
|}.
