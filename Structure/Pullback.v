Require Export Base.

Definition is_pullback {C: Category} {S A B T: C} (f: A ~> T) (g: B ~> T) (p1: S ~> A) (p2: S ~> B) :=
  f ∘ p1 = g ∘ p2 /\
  forall (Z: C) (q1: Z ~> A) (q2: Z ~> B), f ∘ q1 = g ∘ q2 -> exists! u: Z ~> S, p1 ∘ u = q1 /\ p2 ∘ u = q2.

Lemma is_pullback_sym {C: Category} {S A B T: C} (f: A ~> T) (g: B ~> T) (p1: S ~> A) (p2: S ~> B):
  is_pullback f g p1 p2 <-> is_pullback g f p2 p1.
Proof.
  revert S A B T f g p1 p2.
  enough (forall (S A B T: C) (f: A ~> T) (g: B ~> T) (p1: S ~> A) (p2: S ~> B), is_pullback f g p1 p2 -> is_pullback g f p2 p1).
  split; apply H.
  intros.
  split; [apply proj1 in H | apply proj2 in H].
  now symmetry.
  intros Z q2 q1 Hq.
  specialize (H Z q1 q2 (eq_sym Hq)).
  clear Hq.
  destruct H as [u H].
  exists u.
  split; [apply proj1 in H | apply proj2 in H].
  easy.
  intros u' Hu.
  now apply H.
Qed.
