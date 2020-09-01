Require Export Sets.

Program Definition Rel: Category := {|
  obj := set;
  hom X Y := forall x y: set, {P: Prop | P -> x ∈ X /\ y ∈ Y};
  id X x y := x ∈ X /\ x = y;
  comp X Y Z R Q x z := exists y, R y z /\ Q x y;
|}.
Next Obligation.
  apply (proj2_sig (R H z)) in H0.
  apply (proj2_sig (Q x H)) in H1.
  now split.
Qed.
Next Obligation.
  rename a into A, b into B, c into C, d into D.
  extensionality a.
  extensionality d.
  apply eq_sig_hprop.
  intro.
  apply proof_irrelevance.
  simpl.
  apply propositional_extensionality.
  split.
  + intros [c [cd [b [bc ab]]]].
    exists b; split.
    exists c; split.
    all: assumption.
  + intros [b [[c [cd bc]] ab]].
    1: exists c; split.
    2: exists b; split.
    all: assumption.
Qed.
Next Obligation.
  rename a into A, b into B.
  extensionality a.
  extensionality b.
  apply eq_sig_hprop.
  intro.
  apply proof_irrelevance.
  simpl.
  apply propositional_extensionality.
  split.
  + intros [b' [[_ Hb] ab]].
    now subst b'.
  + intros ab.
    exists b.
    repeat split.
    apply (proj2_sig (f a b)).
    all: exact ab.
Qed.
Next Obligation.
  rename a into A, b into B.
  extensionality a.
  extensionality b.
  apply eq_sig_hprop.
  intro.
  apply proof_irrelevance.
  simpl.
  apply propositional_extensionality.
  split.
  + intros [a' [ab [_ Ha]]].
    now subst a'.
  + intros ab.
    exists a.
    repeat split.
    2: apply (proj2_sig (f a b)).
    all: exact ab.
Qed.
