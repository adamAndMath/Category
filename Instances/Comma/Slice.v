Require Export Cat.
Require Export Categories.Slice.
Require Export Categories.Comma.

Program Definition Comma2Slice {C: Category} (c: C): id C ↓ @Δ _ 1 c ~> C / c := {|
  fobj x := {|
    Slice.dom := Comma.source x;
    Slice.arr := Comma.morph x;
  |};
  fmap x y f := {|
    Slice.map := Comma.smap f;
  |};
|}.
Next Obligation.
  rewrite <- comp_id_l.
  symmetry.
  change (Category.obj (id C ↓ @Δ _ 1 c)) in x, y.
  change (fmap (Δ c) (Comma.tmap f) ∘ Comma.morph x = Comma.morph y ∘ fmap (id C) (Comma.smap f)).
  apply Comma.comm.
Qed.
Next Obligation.
  now apply Slice.hom_eq.
Qed.
Next Obligation.
  now apply Slice.hom_eq.
Qed.

Program Definition Slice2Comma {C: Category} (c: C): Functor (C / c) (id C ↓ @Δ _ 1 c) := {|
  fobj x := {|
    Comma.source := Slice.dom x;
    Comma.target := tt;
    Comma.morph := Slice.arr x;
  |};
  fmap x y f := {|
    Comma.smap := Slice.map f;
    Comma.tmap := id tt;
  |};
|}.
Next Obligation.
  rewrite comp_id_l.
  symmetry.
  apply Slice.comm.
Qed.
Next Obligation.
  now apply Comma.hom_eq.
Qed.
Next Obligation.
  now apply Comma.hom_eq.
Qed.

Lemma comma_slice_inv {C: Category} (c: C): Comma2Slice c ∘ Slice2Comma c = id (C / c).
Proof.
  fun_eq x y f.
  now destruct x.
  destruct x as [x x'], y as [y y'].
  simpl in *.
  rewrite !eq_iso_refl.
  simpl.
  clear H H0.
  rewrite comp_id_l, comp_id_r.
  apply Slice.hom_eq; simpl.
  reflexivity.
Qed.

Lemma slice_comma_inv {C: Category} (c: C): Slice2Comma c ∘ Comma2Slice c = id (id C ↓ Δ c).
Proof.
  fun_eq x y f.
  now destruct x, target.
  destruct x as [x [] x'], y as [y [] y'].
  simpl in *.
  rewrite !eq_iso_refl.
  simpl.
  clear H H0.
  etransitivity.
  apply comp_id_l.
  rewrite comp_id_r.
  apply Comma.hom_eq; simpl; split.
  reflexivity.
  apply unit_eq.
Qed.

Canonical CommaSlice {C: Category} (c: C): id C ↓ @Δ _ 1 c <~> C / c :=
  Isomorphism.Pack (Comma2Slice c) (Isomorphism.Mixin _ _ _ (Comma2Slice c) (Slice2Comma c) (slice_comma_inv c) (comma_slice_inv c)).

Program Definition Comma2Coslice {C: Category} (c: C): @Δ _ 1 c ↓ id C ~> C \ c := {|
  fobj (x: @Δ _ 1 c ↓ id C) := {|
    Coslice.cod := Comma.target x;
    Coslice.arr := Comma.morph x;
  |};
  fmap x y f := {|
    Coslice.map := Comma.tmap f;
  |};
|}.
Next Obligation.
  change (Comma.tmap f ∘ Comma.morph x = Comma.morph y).
  change (Category.obj (@Δ _ 1 c ↓ id C)) in x, y.
  rewrite <- comp_id_r.
  change (fmap (id C) (Comma.tmap f) ∘ Comma.morph x = Comma.morph y ∘ fmap (Δ c) (Comma.smap f)).
  apply Comma.comm.
Qed.
Next Obligation.
  now apply Coslice.hom_eq.
Qed.
Next Obligation.
  now apply Coslice.hom_eq.
Qed.

Program Definition Coslice2Comma {C: Category} (c: C): Functor (C \ c) (@Δ _ 1 c ↓ id C) := {|
  fobj x := {|
    Comma.source := tt;
    Comma.target := Coslice.cod x;
    Comma.morph := Coslice.arr x;
  |};
  fmap x y f := {|
    Comma.smap := id tt;
    Comma.tmap := Coslice.map f;
  |};
|}.
Next Obligation.
  rewrite comp_id_r.
  exact (Coslice.comm f).
Qed.
Next Obligation.
  now apply Comma.hom_eq.
Qed.
Next Obligation.
  now apply Comma.hom_eq.
Qed.

Lemma comma_coslice_inv {C: Category} (c: C): Comma2Coslice c ∘ Coslice2Comma c = id (C \ c).
Proof.
  fun_eq x y f.
  now destruct x.
  destruct x as [x x'], y as [y y'].
  simpl in *.
  rewrite !eq_iso_refl.
  simpl.
  clear H H0.
  rewrite comp_id_l, comp_id_r.
  apply Coslice.hom_eq; simpl.
  reflexivity.
Qed.

Lemma coslice_comma_inv {C: Category} (c: C): Coslice2Comma c ∘ Comma2Coslice c = id (Δ c ↓ id C).
Proof.
  fun_eq x y f.
  now destruct x, source.
  destruct x as [[] x x'], y as [[] y y'].
  simpl in *.
  rewrite !eq_iso_refl.
  simpl.
  clear H H0.
  etransitivity.
  apply comp_id_l.
  rewrite comp_id_r.
  apply Comma.hom_eq; simpl; split.
  apply unit_eq.
  reflexivity.
Qed.

Canonical CommaCoslice {C: Category} (c: C): @Δ _ 1 c ↓ id C <~> C \ c :=
  Isomorphism.Pack (Comma2Coslice c) (Isomorphism.Mixin _ _ _ (Comma2Coslice c) (Coslice2Comma c) (coslice_comma_inv c) (comma_coslice_inv c)).
