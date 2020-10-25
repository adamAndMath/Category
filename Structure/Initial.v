Require Export Base.

Definition is_initial {C: Category} (o: C) :=
  forall x: C, exists f: o ~> x, forall g, f = g.

Definition ex_initial (C: Category) :=
  exists x: C, is_initial x.

Instance is_initial_iso (C: Category): Proper (isomorphic C ==> iff) is_initial.
Proof.
  enough (Proper (isomorphic C ==> impl) is_initial).
  now split; apply H.
  intros X Y [i] H Z.
  specialize (H Z).
  destruct H as [f H].
  exists (f ∘ i⁻¹).
  intros g.
  specialize (H (g ∘ i)).
  subst f.
  rewrite <- comp_assoc.
  rewrite inv_r.
  apply comp_id_r.
Qed.

Lemma initial_euniqueness (C: Category): euniqueness (@is_initial C).
Proof.
  intros x y Hx Hy.
  destruct (Hx y) as [f _].
  destruct (Hy x) as [g _].
  specialize (Hx x).
  specialize (Hy y).
  destruct Hx as [x' Hx].
  destruct Hy as [y' Hy].
  constructor.
  exists f, g.
  transitivity x'.
  symmetry.
  1, 2: apply Hx.
  transitivity y'.
  symmetry.
  all: apply Hy.
Qed.

Lemma ex_initial_eunique (C: Category): ex_initial C <-> exists!! x: C, is_initial x.
Proof.
  rewrite <- eunique_existence.
  split.
  + intros H.
    split.
    exact (is_initial_iso C).
    split.
    exact H.
    exact (initial_euniqueness C).
  + intros [_ [H _]].
    exact H.
Qed.

Instance ex_initial_iso: Proper (isomorphic Cat ==> iff) ex_initial.
Proof.
  enough (Proper (isomorphic Cat ==> impl) ex_initial).
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

Module BotCategory.

Structure mixin_of (C: Category) := Mixin {
  zero: C;
  from_zero {a: C}: zero ~> a;
  from_zero_unique (a: C) (f: zero ~> a): from_zero = f;
}.

Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type := Pack { sort: Category; _: class_of sort }.
Local Coercion sort: type >-> Category.

Variable T: type.
Definition class := match T return class_of T with Pack _ c => c end.

Definition Cat: Cat := T.

End ClassDef.

Module Exports.

Coercion sort: type >-> Category.
Coercion Cat: type >-> Category.obj.
Notation BotCategory := type.

End Exports.

End BotCategory.

Export BotCategory.Exports.

Section Initial.
Context {C: BotCategory}.

Definition zero: C := BotCategory.zero C (BotCategory.class C).
Definition from_zero: forall {a: C}, zero ~> a := @BotCategory.from_zero C (BotCategory.class C).

Lemma from_zero_unique {a: C} (f: zero ~> a): from_zero = f.
Proof. apply BotCategory.from_zero_unique. Qed.

Lemma from_zero_comp {a b: C} (f: a ~> b): f ∘ from_zero = from_zero.
Proof.
  symmetry.
  apply from_zero_unique.
Qed.

Lemma zero_to_zero: @from_zero zero = id zero.
Proof. apply from_zero_unique. Qed.

Lemma from_zero_eq {a: C} (f g: zero ~> a): f = g.
Proof.
  transitivity (@from_zero a).
  symmetry.
  all: apply from_zero_unique.
Qed.

End Initial.

Notation "0" := zero.
Notation "¡" := from_zero.

Lemma initial_correct C: inhabited (BotCategory.mixin_of C) <-> ex_initial C.
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
