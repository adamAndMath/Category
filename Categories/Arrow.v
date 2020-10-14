Require Export Two.

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

Section TwoFun.
Context (C: Category).

Program Definition TwoFun_to: Arrow C ~> Fun 2 C := {|
  fobj x := Two.F (Arrow.arr x);
  fmap x y f := {|
    transform b := 
      match b return (if b then Arrow.cod x else Arrow.dom x) ~> (if b then Arrow.cod y else Arrow.dom y) with
      | false => Arrow.fdom f
      | true => Arrow.fcod f
      end;
  |};
|}.
Next Obligation.
  destruct x0, y0, f0.
  1, 3: rewrite comp_id_l.
  1, 2: apply comp_id_r.
  apply Arrow.comm.
Qed.
Next Obligation.
  natural_eq b.
  now destruct b.
Qed.
Next Obligation.
  natural_eq x.
  now destruct x.
Qed.

Program Definition TwoFun_from: Fun 2 C ~> Arrow C := {|
  fobj F := {|
    Arrow.dom := F false;
    Arrow.cod := F true;
    Arrow.arr := fmap F (tt: (false: 2) ~> true);
  |};
  fmap F G η := {|
    Arrow.fdom := η false;
    Arrow.fcod := η true;
  |};
|}.
Next Obligation.
  apply naturality.
Qed.
Next Obligation.
  now apply Arrow.hom_eq.
Qed.
Next Obligation.
  now apply Arrow.hom_eq.
Qed.

Lemma TwoFun_inv_l: TwoFun_from ∘ TwoFun_to = id (Arrow C).
Proof.
  fun_eq x y F.
  now destruct x.
  destruct x as [x x' f].
  destruct y as [y y' g].
  rewrite !eq_iso_refl.
  clear H H0.
  simpl.
  rewrite comp_id_l, comp_id_r.
  now apply Arrow.hom_eq.
Qed.

Lemma TwoFun_inv_r: TwoFun_to ∘ TwoFun_from = id (Fun 2 C).
Proof.
  fun_eq F G η.
  destruct (Two.F_unique x) as [a [b [f H]]].
  now subst x.
  destruct (Two.F_unique F) as [x [x' [f HF]]].
  destruct (Two.F_unique G) as [y [y' [g HG]]].
  subst F G.
  rewrite !eq_iso_refl.
  clear H H0.
  simpl.
  rewrite comp_id_l, comp_id_r.
  natural_eq b.
  now destruct b.
Qed.

Definition TwoFun: Arrow C <~> Fun 2 C :=
  Isomorphism.Pack TwoFun_to (Isomorphism.Mixin _ _ _ TwoFun_to TwoFun_from TwoFun_inv_l TwoFun_inv_r).

Lemma Arrow_is_Fun: Arrow C ≃ Fun 2 C.
Proof.
  constructor.
  exact TwoFun.
Qed.
End TwoFun.
