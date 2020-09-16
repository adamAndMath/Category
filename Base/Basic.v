Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.PropExtensionality.
Require Export Coq.Logic.Classical.
Require Export Coq.Logic.Epsilon.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Program.Basics.
Require Export Coq.Program.Tactics.
Global Set Universe Polymorphism.

Lemma dec (P: Prop): {P} + {~P}.
Proof.
  enough (inhabited ({P} + {~P})).
  destruct (epsilon H (fun _ => True)).
  now left.
  now right.
  destruct (classic P).
  all: constructor.
  now left.
  now right.
Qed.

Lemma eq_sig {T} {P: T -> Prop} (x y: sig P): x = y <-> proj1_sig x = proj1_sig y.
Proof.
  split; intros H.
  now f_equal.
  apply eq_sig_hprop.
  intro.
  apply proof_irrelevance.
  exact H.
Qed.