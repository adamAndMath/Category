Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.PropExtensionality.
Require Export Coq.Logic.Classical.
Require Export Coq.Logic.Epsilon.
Require Export Coq.Classes.Morphisms.
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
