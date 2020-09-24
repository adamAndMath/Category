Require Export Cat.
Require Export Instances.Arrow.
Require Export Comma.

Program Definition Comma2Arrow (C: Category): id C ↓ id C ~> Arrow C := {|
  fobj x := {|
    dom := Comma.source x;
    cod := Comma.target x;
    arr := Comma.morph x;
  |};
  fmap x y f := {|
    fdom := Comma.smap f;
    fcod := Comma.tmap f;
    arr_comm := Comma.comm _ _ x y f;
  |};
|}.
Next Obligation.
  now apply arrow_hom_eq.
Qed.
Next Obligation.
  now apply arrow_hom_eq.
Qed.

Program Definition Arrow2Comma (C: Category): Arrow C ~> id C ↓ id C := {|
  fobj x := {|
    Comma.source := dom x;
    Comma.target := cod x;
    Comma.morph := arr x;
  |};
  fmap x y f := {|
    Comma.smap := fdom f;
    Comma.tmap := fcod f;
    Comma.comm := arr_comm f;
  |};
|}.
Next Obligation.
  now apply Comma.hom_eq.
Qed.
Next Obligation.
  now apply Comma.hom_eq.
Qed.

Lemma comma_arrow_inv (C: Category): Comma2Arrow C ∘ Arrow2Comma C = id (Arrow C).
Proof.
  fun_eq x y f.
  now destruct x.
  destruct x as [dx cx x], y as [dy cy y].
  simpl in *.
  rewrite !eq_iso_refl.
  simpl.
  clear H H0.
  rewrite comp_id_l, comp_id_r.
  now apply arrow_hom_eq.
Qed.

Lemma arrow_comma_inv (C: Category): Arrow2Comma C ∘ Comma2Arrow C = id (id C ↓ id C).
Proof.
  fun_eq x y f.
  now destruct x.
  destruct x as [dx cx x], y as [dy cy y].
  simpl in *.
  rewrite !eq_iso_refl.
  simpl.
  clear H H0.
  rewrite comp_id_l, comp_id_r.
  now apply Comma.hom_eq.
Qed.

Canonical CommaArrow (C: Category): id C ↓ id C <~> Arrow C :=
  Isomorphism.Pack (Comma2Arrow C) (Isomorphism.Mixin _ _ _ (Comma2Arrow C) (Arrow2Comma C) (arrow_comma_inv C) (comma_arrow_inv C)).
