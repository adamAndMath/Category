Require Export Limit.

Definition FreeProd {C: Category}: C ~> C × C := {|
  fobj x := (x, x);
  fmap x y f := (f, f);
  fmap_id _ := eq_refl;
  fmap_comp _ _ _ _ _ := eq_refl;
|}.

Section Prod2Limit.
Context (C: ProdCategory).

Program Definition ProdLim: C × C ~> C := {|
  fobj p := fst p × snd p;
  fmap p q f := fst f (×) snd f;
|}.
Next Obligation.
  apply fprod_id.
Qed.
Next Obligation.
  symmetry.
  apply fprod_comp.
Qed.

Program Definition ProdUnit: id C ~> ProdLim ∘ FreeProd := {|
  transform x := ⟨id x, id x⟩;
|}.
Next Obligation.
  unfold fprod.
  rewrite !fork_comp.
  f_equal.
  all: rewrite <- comp_assoc.
  1: rewrite pi1_fork.
  2: rewrite pi2_fork.
  all: rewrite comp_id_r.
  all: apply comp_id_l.
Qed.

Program Definition ProdCounit: FreeProd ∘ ProdLim ~> id (C × C) := {|
  transform p := (π₁, π₂);
  naturality p q f := _;
|}.
Next Obligation.
  apply Prod.hom_eq; simpl.
  split.
  all: unfold fprod.
  apply pi1_fork.
  apply pi2_fork.
Qed.

Lemma prod_adjoint_by: adjoint_by FreeProd ProdLim ProdCounit ProdUnit.
Proof.
  apply adjoint_by_alt; simpl; split.
  intros x.
  apply Prod.hom_eq; simpl.
  split.
  apply pi1_fork.
  apply pi2_fork.
  intros [x y]; simpl.
  rewrite <- fprod_id at 3.
  unfold fprod.
  rewrite fork_comp.
  f_equal.
  all: rewrite comp_id_l, <- comp_id_r.
  all: rewrite <- comp_assoc.
  all: f_equal.
  apply pi1_fork.
  apply pi2_fork.
Qed.

Lemma prod_adjoint: FreeProd -| ProdLim.
Proof.
  exists ProdCounit, ProdUnit.
  exact prod_adjoint_by.
Qed.

Lemma prod_ex_lim: ex_lim ((1: Cat) + 1) C.
Proof.
  exists (ProdLim ∘ (Fun1C (C: Category) (×) Fun1C C) ∘ FunPlusC 1 1 (C: Category)).
  red.
  rewrite <- comp_assoc.
  replace (@Δ C ((1: Category) + 1)) with ((FunPlusC 1 1 (C: Category))⁻¹ ∘ ((Fun1C C)⁻¹ (×) (Fun1C C)⁻¹) ∘ FreeProd).
  apply adjoint_comp.
  exact prod_adjoint.
  apply adjoint_comp.
  1, 2: apply iso_adjoint.
  fun_eq x y f.
  fun_eq a b f.
  now destruct x0.
  destruct a as [[] | []], b as [[] | []], f.
  1, 2: now rewrite !eq_iso_refl.
  natural_eq p.
  destruct p as [[] | []].
  all: etransitivity.
  1, 3: etransitivity.
  1, 3: apply (f_equal (fun f => f ∘ _)).
  5, 6: apply f_equal.
  5, 6: symmetry.
  1, 2, 5, 6: apply is_eq_refl.
  1: apply (transform_is_eq (eq_iso H0) (inl tt)).
  2: apply (transform_is_eq (eq_iso H0) (inr tt)).
  3: apply (transform_is_eq (eq_iso H) (inl tt)).
  4: apply (transform_is_eq (eq_iso H) (inr tt)).
  1, 2, 3, 4: apply eq_iso_is_eq.
  all: rewrite comp_id_r.
  all: apply comp_id_l.
Qed.
End Prod2Limit.

Section Limit2Prod.
Context (C: Category) (Lim: C × C ~> C) (η: FreeProd ∘ Lim ~> id (C × C)) (ɛ: id C ~> Lim ∘ FreeProd) (adj: adjoint_by FreeProd Lim η ɛ).

Program Definition Limit2Prod_mixin: ProdCategory.mixin_of C :=
  ProdCategory.Mixin C (fun x y => Lim (x, y)) (fun x y z f g => fmap Lim (f, g) ∘ ɛ x) (fun x y => fst (η (x, y))) (fun x y => snd (η (x, y))) _.
Next Obligation.
  apply adjoint_by_alt in adj.
  simpl in adj.
  destruct adj as [adj1 adj2].
  clear adj.
  split.
  intros H.
  2: intros [Hf Hg].
  subst h.
  2: subst f g.
  split.
  + rewrite comp_assoc.
    change (fst (η (b, c) ∘ fmap (FreeProd ∘ Lim) ((f, g): (_, _) ~> (_, _))) ∘ ɛ a = f).
    rewrite naturality.
    simpl.
    rewrite <- comp_assoc.
    change (f ∘ fst (η (a, a) ∘ ((ɛ a, ɛ a): (_, _) ~> (_, _))) = f).
    rewrite adj1.
    apply comp_id_r.
  + rewrite comp_assoc.
    change (snd (η (b, c) ∘ fmap (FreeProd ∘ Lim) ((f, g): (_, _) ~> (_, _))) ∘ ɛ a = g).
    rewrite naturality.
    simpl.
    rewrite <- comp_assoc.
    change (g ∘ snd (η (a, a) ∘ ((ɛ a, ɛ a): (_, _) ~> (_, _))) = g).
    rewrite adj1.
    apply comp_id_r.
  + change (h = fmap Lim (η (b, c) ∘ fmap FreeProd h) ∘ ɛ a).
    rewrite fmap_comp.
    change (h = fmap Lim (η (b, c)) ∘ fmap (Lim ∘ FreeProd) h ∘ ɛ a).
    rewrite <- comp_assoc.
    setoid_rewrite <- (naturality ɛ h).
    rewrite comp_assoc.
    setoid_rewrite (adj2 (b, c)).
    symmetry.
    apply comp_id_l.
Qed.

Definition Limit2Prod: ProdCategory :=
  ProdCategory.Pack C Limit2Prod_mixin.
End Limit2Prod.

Lemma prod_limit (C: Category): ex_lim ((1: Category) + 1) C <-> inhabited (ProdCategory.mixin_of C).
Proof.
  split.
  + intros [L adj].
    red in adj.
    assert (exists Lim: C × C ~> C, Lim ∘ (Fun1C C (×) Fun1C C) ∘ FunPlusC 1 1 C = L).
    exists (L ∘ (FunPlusC 1 1 C)⁻¹ ∘ ((Fun1C C)⁻¹ (×) (Fun1C C)⁻¹)).
    rewrite <- (comp_assoc (L ∘ _)).
    rewrite fprod_comp.
    rewrite inv_l, fprod_id, comp_id_r.
    rewrite <- comp_assoc.
    rewrite inv_l.
    apply comp_id_r.
    destruct H as [Lim H].
    subst L.
    replace (@Δ C ((1: Category) + 1)) with ((FunPlusC 1 1 C)⁻¹ ∘ ((Fun1C C)⁻¹ (×) (Fun1C C)⁻¹) ∘ FreeProd) in adj.
    rewrite <- comp_assoc in adj.
    apply adjoint_comp_iso_r in adj.
    apply (adjoint_comp_iso_r _ _ (iprod (Fun1C C) (Fun1C C))) in adj.
    destruct adj as [η [ɛ adj]].
    constructor.
    exact (Limit2Prod_mixin C Lim η ɛ adj).
    clear.
    fun_eq x y f.
    fun_eq a b f.
    now destruct x0.
    destruct a as [[] | []], b as [[] | []], f.
    1, 2: now rewrite !eq_iso_refl.
    natural_eq a.
    destruct a as [[] | []].
    all: etransitivity.
    1, 3: etransitivity.
    1, 3: apply (f_equal (fun f => f ∘ _)).
    5, 6: apply f_equal.
    5, 6: symmetry.
    1, 2, 5, 6: apply is_eq_refl.
    1: apply (transform_is_eq (eq_iso H0) (inl tt)).
    2: apply (transform_is_eq (eq_iso H0) (inr tt)).
    3: apply (transform_is_eq (eq_iso H) (inl tt)).
    4: apply (transform_is_eq (eq_iso H) (inr tt)).
    1, 2, 3, 4: apply eq_iso_is_eq.
    all: rewrite comp_id_r.
    all: apply comp_id_l.
  + intros [m].
    exact (prod_ex_lim (ProdCategory.Pack C m)).
Qed.
