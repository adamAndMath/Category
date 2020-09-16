Require Export Diagram.Parallel.
Require Export Limit.
Require Export Instances.

Section ex1.
Context {T: Type} (R: T -> T -> Prop) {pre: PreOrder R} (po: PartialOrder eq R).

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
