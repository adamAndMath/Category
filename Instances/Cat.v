Require Export Cat.Terminal.
Require Export Cat.Initial.
Require Export Cat.Product.
Require Export Cat.Coproduct.

Section Fun_0_l.
Lemma Fun0C_inv_l (C: Category): Δ (from_zero: 0 ~> C) ∘ to_one = id (Fun 0 C).
Proof.
  fun_eq F G η.
  apply (@from_zero_unique _ C).
  subst F G.
  simpl.
  rewrite comp_id_l, comp_id_r.
  natural_eq x.
  destruct x.
Qed.

Lemma Fun0C_inv_r (C: Category): to_one ∘ Δ (from_zero: 0 ~> C) = id 1.
Proof.
  fun_eq x y f.
  apply unit_unique.
  apply unit_eq.
Qed.

Canonical Fun0C (C: Category): Fun 0 C <~> 1 :=
  Isomorphism.Pack to_one (Isomorphism.Mixin Cat (Fun 0 C) 1 to_one (Δ (from_zero: 0 ~> C)) (Fun0C_inv_l C) (Fun0C_inv_r C)).

Lemma Fun_0_l (C: Category): Fun 0 C ≃ 1.
Proof.
  constructor.
  exact (Fun0C C).
Qed.
End Fun_0_l.

Section Fun_1_r.
Context (C: Category).

Definition FunC1_to: Fun C 1 ~> 1 := Δ tt.
Definition FunC1_from: 1 ~> Fun C 1 := Δ.

Lemma FunC1_inv_l: FunC1_from ∘ FunC1_to = id (Fun C 1).
Proof.
  fun_eq F G η.
  apply (to_one_unique x).
  natural_eq x.
  apply unit_eq.
Qed.

Lemma FunC1_inv_r: FunC1_to ∘ FunC1_from = id 1.
Proof.
  fun_eq x y f.
  apply unit_unique.
  apply unit_eq.
Qed.

Definition FunC1_mixin: Isomorphism.mixin_of (FunC1_to) :=
  Isomorphism.Mixin Cat (Fun C 1) 1 FunC1_to FunC1_from FunC1_inv_l FunC1_inv_r.

Definition FunC1: Fun C 1 <~> 1 :=
  Isomorphism.Pack FunC1_to FunC1_mixin.

Lemma Fun_1_r: Fun C 1 ≃ 1.
Proof.
  constructor.
  exact FunC1.
Qed.
End Fun_1_r.

Section Fun_1_l.
Context (C: Category).

Definition Fun1C_to: Fun 1 C ~> C := {|
  fobj (F: Fun 1 C) := F tt;
  fmap F G η := η tt;
  fmap_id _ := eq_refl;
  fmap_comp _ _ _ _ _ := eq_refl;
|}.

Definition Fun1C_from: C ~> Fun 1 C := Δ.

Lemma Fun1C_inv_l: Fun1C_from ∘ Fun1C_to = id (Fun 1 C).
Proof.
  fun_eq F G η.
  rename x into F.
  fun_eq x y f.
  f_equal.
  apply unit_unique.
  destruct x, y, f.
  rewrite !eq_iso_refl.
  clear H H0.
  simpl.
  rewrite !comp_id_r.
  symmetry.
  apply (@fmap_id _ _ F).
  natural_eq x.
  destruct x.
  rewrite (is_eq_refl (to (eq_iso H) tt)).
  rewrite (is_eq_refl (to (eq_iso H0) tt)).
  simpl.
  rewrite comp_id_r.
  apply comp_id_l.
  1: destruct H0.
  2: destruct H.
  all: simpl.
  all: apply is_eq_id.
Qed.

Lemma Fun1C_inv_r: Fun1C_to ∘ Fun1C_from = id C.
Proof. now fun_eq x y f. Qed.

Definition Fun1C: Fun 1 C <~> C :=
  Isomorphism.Pack Fun1C_to (Isomorphism.Mixin Cat (Fun 1 C) C Fun1C_to Fun1C_from Fun1C_inv_l Fun1C_inv_r).

Lemma Fun_1_l: Fun 1 C ≃ C.
Proof.
  constructor.
  exact Fun1C.
Qed.
End Fun_1_l.

Section Fun_plus_l.

Definition FunPlusC_to (C D T: Category): Fun (C + D) T ~> Fun C T × Fun D T :=
  ⟨Comp_r in1, Comp_r in2⟩.

Program Definition FunPlusC_from (C D T: Category): Fun C T × Fun D T ~> Fun (C + D) T := {|
  fobj F := [fst F, snd F];
  fmap F G η := {|
    transform x :=
      match x return [fst F, snd F] x ~> [fst G, snd G] x with
      | inl x => fst η x
      | inr x => snd η x
      end;
  |};
|}.
Next Obligation.
  destruct x as [x | x], y as [y | y]; simpl.
  2, 3: destruct f.
  all: apply naturality.
Qed.
Next Obligation.
  natural_eq x.
  destruct x as [x | x].
  all: reflexivity.
Qed.
Next Obligation.
  natural_eq x.
  destruct x as [x | x].
  all: reflexivity.
Qed.

Lemma FunPlusC_inv_l (C D T: Category): FunPlusC_from C D T ∘ FunPlusC_to C D T = id (Fun (C + D) T).
Proof.
  fun_eq F G η.
  symmetry.
  now apply (merge_in _ _ x).
  natural_eq x.
  destruct x as [x | x].
  2: rewrite (is_eq_refl (to (eq_iso H) (inr x))).
  2: rewrite (is_eq_refl (to (eq_iso H0) (inr x))).
  rewrite (is_eq_refl (to (eq_iso H) (inl x))).
  rewrite (is_eq_refl (to (eq_iso H0) (inl x))).
  1, 4: simpl.
  1, 2: rewrite comp_id_r.
  1, 2: apply comp_id_l.
  1, 3: apply (transform_is_eq (eq_iso H0)).
  3, 4: apply (transform_is_eq (eq_iso H)).
  all: apply eq_iso_is_eq.
Qed.

Lemma FunPlusC_inv_r (C D T: Category): FunPlusC_to C D T ∘ FunPlusC_from C D T = id (Fun C T × Fun D T).
Proof.
  rewrite <- fprod_id.
  apply fork_pi; split.
  all: rewrite comp_assoc, comp_id_l.
  all: unfold FunPlusC_to.
  1: rewrite pi1_fork.
  2: rewrite pi2_fork.
  all: fun_eq F G η.
  1: apply (merge_in1 (fst x) (snd x)).
  2: apply (merge_in2 (fst x) (snd x)).
  all: natural_eq x.
  all: rewrite (is_eq_refl (to (eq_iso H) x)).
  1, 3: rewrite (is_eq_refl (to (eq_iso H0) x)).
  1, 3: simpl.
  1, 2: rewrite comp_id_r.
  1, 2: apply comp_id_l.
  1, 2: apply (transform_is_eq (eq_iso H0)).
  3, 4: apply (transform_is_eq (eq_iso H)).
  all: apply eq_iso_is_eq.
Qed.

Definition FunPlusC (C D T: Category): Fun (C + D) T <~> Fun C T × Fun D T :=
  Isomorphism.Pack (FunPlusC_to C D T) (Isomorphism.Mixin _ _ _ (FunPlusC_to C D T) (FunPlusC_from C D T) (FunPlusC_inv_l C D T) (FunPlusC_inv_r C D T)).

Lemma Fun_plus_l (C D T: Category): Fun (C + D) T ≃ Fun C T × Fun D T.
Proof.
  constructor.
  exact (FunPlusC C D T).
Qed.
End Fun_plus_l.

Section Fun_prod_r.

Definition FunCProd_to (S C D: Category): Fun S (C × D) ~> Fun S C × Fun S D :=
  ⟨Comp_l π₁, Comp_l π₂⟩.

Program Definition FunCProd_from (S C D: Category): Fun S C × Fun S D ~> Fun S (C × D) := {|
  fobj F := ⟨fst F, snd F⟩;
  fmap F G η := {|
    transform x := (fst η x, snd η x);
  |};
|}.
Next Obligation.
  unfold comp; simpl.
  f_equal.
  all: apply naturality.
Qed.
Next Obligation.
  now natural_eq x.
Qed.
Next Obligation.
  now natural_eq x.
Qed.

Lemma FunCProd_inv_l (S C D: Category): FunCProd_from S C D ∘ FunCProd_to S C D = id (Fun S (C × D)).
Proof.
  fun_eq F G η.
  symmetry.
  now apply (fork_pi _ _ x).
  natural_eq x.
  apply Prod.hom_eq; simpl.
  split.
  all: etransitivity.
  2, 3: etransitivity.
  1, 4: apply (f_equal (fun f => f ∘ _)).
  4, 6: apply f_equal.
  4, 5: symmetry.
  1, 2, 4, 5: apply is_eq_refl.
  1, 2: destruct H0.
  3, 4: destruct H.
  1, 2, 3, 4: apply is_eq_id.
  all: rewrite comp_id_r.
  all: apply comp_id_l.
Qed.

Lemma FunCProd_inv_r (S C D: Category): FunCProd_to S C D ∘ FunCProd_from S C D = id (Fun S C × Fun S D).
Proof.
  rewrite <- fprod_id.
  apply fork_pi; split.
  all: rewrite comp_assoc, comp_id_l.
  all: unfold FunCProd_to.
  1: rewrite pi1_fork.
  2: rewrite pi2_fork.
  all: fun_eq F G η.
  1: apply (pi1_fork (fst x) (snd x)).
  2: apply (pi2_fork (fst x) (snd x)).
  all: natural_eq x.
  all: rewrite (is_eq_refl (to (eq_iso H) x)).
  1, 3: rewrite (is_eq_refl (to (eq_iso H0) x)).
  1, 3: simpl.
  1, 2: rewrite comp_id_r.
  1, 2: apply comp_id_l.
  1, 2: apply (transform_is_eq (eq_iso H0)).
  3, 4: apply (transform_is_eq (eq_iso H)).
  all: apply eq_iso_is_eq.
Qed.

Definition FunCProd (S C D: Category): Fun S (C × D) <~> Fun S C × Fun S D :=
  Isomorphism.Pack (FunCProd_to S C D) (Isomorphism.Mixin _ _ _ (FunCProd_to S C D) (FunCProd_from S C D) (FunCProd_inv_l S C D) (FunCProd_inv_r S C D)).

Lemma Fun_prod_r (S C D: Category): Fun S (C × D) ≃ Fun S C × Fun S D.
Proof.
  constructor.
  exact (FunCProd S C D).
Qed.
End Fun_prod_r.

Section Curry.

Program Definition Curry_to (C D T: Category): Fun C (Fun D T) ~> Fun (C × D) T := {|
  fobj F := {|
    fobj p := F (fst p) (snd p);
    fmap p q f := fmap (F (fst q)) (snd f) ∘ fmap F (fst f) (snd p);
  |};
  fmap F G η := {|
    transform p := η (fst p) (snd p);
  |};
|}.
Next Obligation.
  simpl.
  rewrite !fmap_id.
  apply comp_id_l.
Qed.
Next Obligation.
  simpl.
  rewrite !fmap_comp.
  simpl.
  rewrite !comp_assoc.
  f_equal.
  rewrite <- !comp_assoc.
  f_equal.
  symmetry.
  apply naturality.
Qed.
Next Obligation.
  rename o1 into x, o into x', o2 into y, o0 into y'.
  simpl.
  rewrite comp_assoc.
  rewrite naturality.
  rewrite <- !comp_assoc.
  f_equal.
  change ((η x' ∘ fmap F (fst f)) y = (fmap G (fst f) ∘ η x) y).
  f_equal.
  apply naturality.
Qed.
Next Obligation.
  now natural_eq x.
Qed.
Next Obligation.
  now natural_eq x.
Qed.

Program Definition Curry_from (C D T: Category): Fun (C × D) T ~> Fun C (Fun D T) := {|
  fobj F := Comp_l F ∘ FProd C D;
  fmap F G η := {|
    transform x := {|
      transform y := η (x, y);
    |};
  |};
|}.
Next Obligation.
  apply naturality.
Qed.
Next Obligation.
  natural_eq a.
  apply naturality.
Qed.
Next Obligation.
  natural_eq x.
  natural_eq y.
  reflexivity.
Qed.
Next Obligation.
  natural_eq x.
  natural_eq y.
  reflexivity.
Qed.

Lemma Curry_inv_l (C D T: Category): Curry_from C D T ∘ Curry_to C D T = id (Fun C (Fun D T)).
Proof.
  fun_eq F G η.
  rename x into F.
  fun_eq x x' f.
  fun_eq y y' g.
  rewrite fmap_id.
  apply comp_id_r.
  natural_eq y.
  rewrite fmap_id, comp_id_l.
  rewrite (is_eq_refl (to (eq_iso H) y)).
  rewrite (is_eq_refl (to (eq_iso H0) y)).
  simpl.
  rewrite comp_id_r.
  apply comp_id_l.
  1: apply (transform_is_eq (eq_iso H0)).
  2: apply (transform_is_eq (eq_iso H)).
  1, 2: apply eq_iso_is_eq.
  natural_eq x.
  natural_eq y.
  etransitivity.
  etransitivity.
  apply (f_equal (fun f => f ∘ _)).
  3: apply f_equal.
  3: symmetry.
  1, 3: apply is_eq_refl.
  1: apply (transform_is_eq (to (eq_iso H0) x)).
  2: apply (transform_is_eq (to (eq_iso H) x)).
  1: apply (transform_is_eq (eq_iso H0)).
  2: apply (transform_is_eq (eq_iso H)).
  1, 2: apply eq_iso_is_eq.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Lemma Curry_inv_r (C D T: Category): Curry_to C D T ∘ Curry_from C D T = id (Fun (C × D) T).
Proof.
  fun_eq F G η.
  rename x into F.
  fun_eq p q f.
  now destruct x.
  destruct p as [x y], q as [x' y'].
  simpl in *.
  rewrite !eq_iso_refl.
  simpl.
  rewrite comp_id_l, comp_id_r.
  rewrite <- fmap_comp.
  f_equal.
  apply Prod.hom_eq; simpl; split.
  apply comp_id_l.
  apply comp_id_r.
  natural_eq p.
  destruct p as [x y].
  simpl.
  rewrite (is_eq_refl (to (eq_iso H) (x, y))).
  rewrite (is_eq_refl (to (eq_iso H0) (x, y))).
  simpl.
  rewrite comp_id_r.
  apply comp_id_l.
  1: apply (transform_is_eq (eq_iso H0)).
  2: apply (transform_is_eq (eq_iso H)).
  all: apply eq_iso_is_eq.
Qed.

Definition Curry (C D T: Category): Fun C (Fun D T) <~> Fun (C × D) T :=
  Isomorphism.Pack (Curry_to C D T) (Isomorphism.Mixin _ _ _ (Curry_to C D T) (Curry_from C D T) (Curry_inv_l C D T) (Curry_inv_r C D T)).

Lemma Fun_prod_l (C D T: Category): Fun C (Fun D T) ≃ Fun (C × D) T.
Proof.
  constructor.
  exact (Curry C D T).
Qed.

End Curry.
