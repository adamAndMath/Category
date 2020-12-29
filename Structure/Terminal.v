Require Export Base.

Definition is_terminal {C: Category} (o: C) :=
  forall x: C, exists f: x ~> o, forall g, f = g.

Definition ex_terminal (C: Category) :=
  exists x: C, is_terminal x.

Instance is_terminal_iso (C: Category): Proper (isomorphic C ==> iff) is_terminal.
Proof.
  enough (Proper (isomorphic C ==> impl) is_terminal).
  now split; apply H.
  intros X Y [i] H Z.
  specialize (H Z).
  destruct H as [f H].
  exists (i ∘ f).
  intros g.
  specialize (H (i⁻¹ ∘ g)).
  subst f.
  rewrite comp_assoc.
  rewrite inv_r.
  apply comp_id_l.
Qed.

Lemma terminal_euniqueness (C: Category): euniqueness (@is_terminal C).
Proof.
  intros x y Hx Hy.
  destruct (Hx y) as [f _].
  destruct (Hy x) as [g _].
  specialize (Hx x).
  specialize (Hy y).
  destruct Hx as [x' Hx].
  destruct Hy as [y' Hy].
  constructor.
  exists g, f.
  transitivity x'.
  symmetry.
  1, 2: apply Hx.
  transitivity y'.
  symmetry.
  all: apply Hy.
Qed.

Lemma ex_terminal_eunique (C: Category): ex_terminal C <-> exists!! x: C, is_terminal x.
Proof.
  rewrite <- eunique_existence.
  split.
  + intros H.
    split.
    exact (is_terminal_iso C).
    split.
    exact H.
    exact (terminal_euniqueness C).
  + intros [_ [H _]].
    exact H.
Qed.

Instance ex_terminal_iso: Proper (isomorphic Cat ==> iff) ex_terminal.
Proof.
  enough (Proper (isomorphic Cat ==> impl) ex_terminal).
  now split; apply H.
  intros C D [I] [o H].
  exists (to I o).
  intros x'.
  destruct (ex_fobj_iso I x') as [x].
  subst x'.
  specialize (H x).
  destruct H as [f H].
  exists (fmap (to I) f).
  intros g'.
  destruct (ex_fmap_iso I g') as [g].
  subst g'.
  f_equal.
  apply H.
Qed.

Module TopCategory.

Structure mixin_of (C: Category) := Mixin {
  one: C;
  to_one {a: C}: a ~> one;
  to_one_unique {a: C} (f: a ~> one): @to_one a = f;
}.

Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type := Pack { sort: Category; _: class_of sort }.
Local Coercion sort: type >-> Category.

Variable T: type.
Definition class := match T return class_of T with Pack _ c => c end.

Definition Cat: Cat := T.

End ClassDef.

Lemma mixin_eq {C: Category} (m n: mixin_of C): m = n <-> one C m = one C n.
Proof.
  split.
  intros H.
  now subst n.
  destruct m as [a f Hf], n as [b g Hg]; simpl.
  intros H.
  subst b.
  enough (f = g).
  subst g.
  f_equal; apply proof_irrelevance.
  extensionality x.
  apply Hf.
Qed.

Module Exports.

Coercion sort: type >-> Category.
Coercion Cat: type >-> Category.obj.
Notation TopCategory := type.

End Exports.

End TopCategory.

Export TopCategory.Exports.

Section Terminal.
Context {C: TopCategory}.

Definition one: C := TopCategory.one C (TopCategory.class C).
Definition to_one: forall {a: C}, a ~> one := @TopCategory.to_one C (TopCategory.class C).

Lemma to_one_unique {a: C} (f: a ~> one): to_one = f.
Proof. apply TopCategory.to_one_unique. Qed.

Lemma to_one_comp {a b: C} (f: a ~> b): to_one ∘ f = to_one.
Proof.
  symmetry.
  apply to_one_unique.
Qed.

Lemma one_to_one: @to_one one = id one.
Proof. apply to_one_unique. Qed.

Lemma to_one_eq {a: C} (f g: a ~> one): f = g.
Proof.
  transitivity (@to_one a).
  symmetry.
  all: apply to_one_unique.
Qed.

Lemma one_is_terminal: is_terminal one.
Proof.
  intros x.
  exists to_one.
  apply to_one_unique.
Qed.

End Terminal.

Notation "1" := one.
Notation "!" := to_one.

Lemma terminal_correct C: inhabited (TopCategory.mixin_of C) <-> ex_terminal C.
Proof.
  split.
  + intros [[o f Hf]].
    exists o.
    intros a.
    exists (f a).
    apply Hf.
  + intros [o H].
    apply ex_forall in H.
    destruct H as [f Hf].
    constructor.
    now exists o f.
Qed.
