Require Export Diagram.Parallel.
Require Export Limit.
Require Export Instances.

Section ex1.
Context {T: Type} (R: T -> T -> Prop) {pre: PreOrder R} (po: PartialOrder eq R).

Definition poset_eq: Fun Parallel (Poset R) ~> Poset R := {|
  fobj (F: Parallel ~> Poset R) := F false;
  fmap _ _ η := η false;
  fmap_id _ := eq_refl;
  fmap_comp _ _ _ _ _ := eq_refl;
|}.

Program Definition poset_eq_eps: Δ ∘ poset_eq ~> id (Fun Parallel (Poset R)) := {|
  transform (F: Parallel ~> Poset R) := {|
    transform (b: Parallel) :=
      match b return Δ (F false) (b: Parallel) ~> F b with
      | false => id (F false)
      | true => fmap F (Parallel.arr false)
      end;
    naturality _ _ _ := Poset_hom_eq _ _;
  |}: (Δ ∘ poset_eq) F ~> id (Fun Parallel (Poset R)) F;
|}.
Next Obligation.
  rename x into F, y into G, f into η.
  natural_eq x.
  apply Poset_hom_eq.
Qed.

Definition poset_eq_eta: id (Poset R) ~> poset_eq ∘ Δ := {|
  transform x := id x: id (Poset R) x ~> (poset_eq ∘ Δ) x;
  naturality _ _ f := eq_trans (comp_id_l f) (eq_sym (comp_id_r f));
|}.

Lemma poset_equalizer: ex_lim Parallel (Poset R).
Proof.
  exists poset_eq.
  exists poset_eq_eps, poset_eq_eta.
  apply adjoint_by_alt.
  split.
  intros x.
  natural_eq b.
  apply Poset_hom_eq.
  intros F.
  apply Poset_hom_eq.
Qed.

Lemma poset_equalizer: has_limit Parallel (Poset R).
Proof.
  intros F.
  unshelve eexists.
  unshelve econstructor.
  exact (F false).
  intros [].
  exact (fmap F arr1).
  exact (fmap F (id _)).
  all: simpl.
  intros.
  apply Poset_hom_eq.
  intros c.
  unshelve eexists.
  unshelve econstructor; simpl.
  exact (edge c false).
  intros.
  apply Poset_hom_eq.
  intros f.
  conemor_eq.
  apply Poset_hom_eq.
Qed.

Local Instance flip_paritalOrder: PartialOrder eq (flip R).
Proof.
  intros x y.
  red.
  rewrite (po x y).
  do 2 split.
  all: apply H.
Qed.

Lemma co_poset: co (Poset R) = Poset (flip R).
Proof.
  unfold co, flip, Poset.
  f_equal.
  apply cat_mixin_eq.
  simpl.
  repeat split.
  all: intros.
  all: apply proof_irrelevance.
Qed.

Lemma poset_coequalizer: has_colimit Parallel (Poset R).
Proof.
  apply has_limit_co.
  intros F.
  unshelve eexists.
  unshelve econstructor.
  exact (F false).
  intros [].
  exact (fmap F arr1).
  exact (fmap F (id _)).
  all: simpl.
  intros.
  apply Poset_hom_eq.
  intros c.
  unshelve eexists.
  unshelve econstructor; simpl.
  exact (edge c false).
  intros.
  apply Poset_hom_eq.
  intros f.
  conemor_eq.
  apply Poset_hom_eq.
Qed.

End ex1.
