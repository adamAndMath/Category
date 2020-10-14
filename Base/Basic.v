Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.PropExtensionality.
Require Export Coq.Logic.Classical.
Require Export Coq.Logic.Epsilon.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Program.Basics.
Require Export Coq.Program.Tactics.
Global Set Universe Polymorphism.
Global Set Polymorphic Inductive Cumulativity.

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

Lemma ex_forall {T} {F: T -> Type} (P: forall x, F x -> Prop): (forall x, exists y, P x y) -> exists (f: forall x, F x), forall x, P x (f x).
Proof.
  intros H.
  assert (forall x, inhabited (F x)) as i.
    intros x.
    now destruct (H x).
  exists (fun x => epsilon (i x) (P x)).
  intros x.
  apply epsilon_spec, H.
Qed.

Lemma inhabit_forall {T} (F: T -> Type): (forall x, inhabited (F x)) -> inhabited (forall x, F x).
Proof.
  intros H.
  constructor.
  intros x.
  exact (epsilon (H x) (fun _ => True)).
Qed.
