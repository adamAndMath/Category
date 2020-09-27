Require Export Base.

Module Arrow.

Section category.
Context (C: Category).

Structure obj := Obj {
  dom: C;
  cod: C;
  arr: dom ~> cod;
}.

Structure hom (f g: obj) := Hom {
  fdom: dom f ~> dom g;
  fcod: cod f ~> cod g;
  comm: fcod ∘ arr f = arr g ∘ fdom;
}.

Lemma obj_eq (f g: obj): f = g <-> dom f = dom g /\ cod f = cod g /\ (forall (ed: dom f = dom g) (ec: cod f = cod g), eq_iso ec ∘ arr f = arr g ∘ eq_iso ed).
Proof.
  split.
  + intros H.
    subst g.
    repeat split.
    intros ed ec.
    rewrite !eq_iso_refl.
    clear ed ec.
    simpl.
    rewrite comp_id_r.
    apply comp_id_l.
  + destruct f as [x y f], g as [x' y' g].
    simpl.
    intros [Hx [Hy H]].
    subst x' y'.
    f_equal.
    rewrite <- comp_id_r, <- (comp_id_l f).
    exact (H eq_refl eq_refl).
Qed.

Lemma hom_eq (f g: obj) (F G: hom f g): F = G <-> fdom _ _ F = fdom _ _ G /\ fcod _ _ F = fcod _ _ G.
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

Definition id (f: obj): hom f f := {|
  fdom := id (dom f);
  fcod := id (cod f);
  comm := eq_trans (comp_id_l (arr f)) (eq_sym (comp_id_r (arr f)));
|}.

Definition comp {f g h: obj} (F: hom g h) (G: hom f g): hom f h := {|
  fdom := fdom _ _ F ∘ fdom _ _ G;
  fcod := fcod _ _ F ∘ fcod _ _ G;
  comm :=
    eq_trans (eq_trans (eq_trans (eq_trans
      (eq_sym (comp_assoc _ _ _))
      (f_equal _ (comm _ _ G)))
      (comp_assoc _ _ _))
      (f_equal (fun f => f ∘ _) (comm _ _ F)))
      (eq_sym (comp_assoc _ _ _));
|}.

Lemma comp_assoc (a b c d: obj) (f: hom c d) (g: hom b c) (h: hom a b): comp f (comp g h) = comp (comp f g) h.
Proof.
  apply hom_eq; split; simpl.
  all: apply comp_assoc.
Qed.

Lemma comp_id_l (f g: obj) (F: hom f g): comp (id g) F = F.
Proof.
  apply hom_eq; split; simpl.
  all: apply comp_id_l.
Qed.

Lemma comp_id_r (f g: obj) (F: hom f g): comp F (id f) = F.
Proof.
  apply hom_eq; split; simpl.
  all: apply comp_id_r.
Qed.

Definition cat_mixin: Category.mixin_of obj :=
  Category.Mixin obj hom id (@comp) comp_assoc comp_id_l comp_id_r.

Canonical cat: Category :=
  Category.Pack obj cat_mixin.

End category.

Arguments dom {C} _.
Arguments cod {C} _.
Arguments arr {C} _.

Arguments fdom {C f g} _.
Arguments fcod {C f g} _.
Arguments comm {C f g} _.

Definition Dom (C: Category): cat C ~> C := {|
  fobj := dom;
  fmap f g := fdom;
  fmap_id f := eq_refl;
  fmap_comp _ _ _ F G := eq_refl;
|}.

Definition Cod (C: Category): cat C ~> C := {|
  fobj := cod;
  fmap f g := fcod;
  fmap_id f := eq_refl;
  fmap_comp _ _ _ F G := eq_refl;
|}.

End Arrow.

Canonical Arrow.cat.
Coercion Arrow.Obj: hom >-> Arrow.obj.
Notation Arrow := Arrow.cat.
