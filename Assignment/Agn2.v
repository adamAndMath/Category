Require Export Diagram.Parallel.
Require Export Limit.
Require Export Instances.

Section ex1.
Context {T: Type}.

Lemma poset_equalizer (R: T -> T -> Prop) {pre: PreOrder R} (po: PartialOrder eq R): has_limit Parallel (Poset R).
Proof.
  intros F.
  unshelve eexists.
  unshelve econstructor.
  exact (F false).
  intros [].
  exact (fmap F (Parallel.arr false)).
  exact (id (F false)).
  intros x y f.
  apply Proset.hom_eq.
  intros N.
  unshelve eexists.
  exists (edge N false).
  simpl.
  intros x.
  apply Proset.hom_eq.
  intros [f Hf].
  simpl in f, Hf.
  conemor_eq.
  apply Proset.hom_eq.
Qed.

Lemma poset_coequalizer (R: T -> T -> Prop) {pre: PreOrder R} (po: PartialOrder eq R): has_colimit Parallel (Poset R).
Proof.
  apply has_limit_co.
  rewrite dual_poset.
  generalize (@poset_equalizer (flip R) _ (PartialOrder_inverse po)).
  apply has_limit_iso.
  symmetry.
  exact Parallel.dual_iso.
  reflexivity.
Qed.

End ex1.
