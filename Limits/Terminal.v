Require Export Limit.

Section Top2Limit.
Context (C: TopCategory).

Definition TopLim: 1 ~> C := Δ 1.

Program Definition TopUnit: id C ~> TopLim ∘ ! := {|
  transform _ := !;
|}.
Next Obligation.
  rewrite comp_id_l.
  symmetry.
  apply to_one_unique.
Qed.

Program Definition TopCounit: ! ∘ TopLim ~> id (1: Cat) := {|
  transform _ := tt;
  naturality _ _ _ := eq_refl;
|}.

Lemma top_adjoint_by: adjoint_by ! TopLim TopCounit TopUnit.
Proof.
  apply adjoint_by_alt; simpl; split.
  all: intros _.
  reflexivity.
  rewrite comp_id_l.
  apply to_one_unique.
Qed.

Lemma top_adjoint: ! -| TopLim.
Proof.
  exists TopCounit, TopUnit.
  exact top_adjoint_by.
Qed.

Lemma top_ex_lim: ex_lim 0 C.
Proof.
  exists (TopLim ∘ Fun0C C).
  red.
  replace (@Δ' C 0) with ((Fun0C C)⁻¹ ∘ @to_one _ C).
  apply adjoint_comp.
  exact top_adjoint.
  apply iso_adjoint.
  fun_eq x y f.
  apply (@from_zero_unique CatBot).
  natural_eq o.
  destruct o.
Qed.
End Top2Limit.

Section Limit2Top.
Context (C: Category) (Lim: 1 ~> C) (η: ! ∘ Lim ~> id (1: Cat)) (ɛ: id C ~> Lim ∘ !) (adj: adjoint_by ! Lim η ɛ).

Program Definition Limit2Top_mixin: TopCategory.mixin_of C :=
  TopCategory.Mixin C (Lim tt) (transform ɛ) _.
Next Obligation.
  apply adjoint_by_alt in adj.
  simpl in adj.
  destruct adj as [adj1 adj2].
  clear adj.
  specialize (adj1 a).
  specialize (adj2 tt).
  rewrite comp_id_r in adj1.
  rewrite adj1 in adj2.
  rewrite fmap_id, comp_id_l in adj2.
  symmetry.
  specialize (naturality ɛ f) as H.
  simpl in H.
  rewrite fmap_id, adj2 in H.
  rewrite !comp_id_l in H.
  exact H.
Qed.

Definition Limit2Top: TopCategory :=
  TopCategory.Pack C Limit2Top_mixin.
End Limit2Top.

Lemma top_limit (C: Category): ex_lim 0 C <-> inhabited (TopCategory.mixin_of C).
Proof.
  split.
  + intros [L adj].
    red in adj.
    assert (exists Lim: 1 ~> C, Lim ∘ Fun0C C = L).
    exists (L ∘ (Fun0C C)⁻¹).
    rewrite <- comp_assoc.
    rewrite inv_l.
    apply comp_id_r.
    destruct H as [Lim H].
    subst L.
    generalize (adjoint_comp _ _ _ _ adj (iso_adjoint (Fun0C C))).
    clear adj; intros adj.
    rewrite <- comp_assoc in adj.
    rewrite inv_r, comp_id_r in adj.
    rewrite <- (to_one_unique (Fun0C C ∘ @Δ' C 0)) in adj.
    destruct adj as [η [ɛ adj]].
    constructor.
    exact (Limit2Top_mixin C Lim η ɛ adj).
  + intros [m].
    exact (top_ex_lim (TopCategory.Pack C m)).
Qed.
