Require Export Base.

Definition is_equalizer {C: Category} {x y: C} (f g: x ~> y) (E: C) (e: E ~> x) :=
  f ∘ e = g ∘ e /\
  forall z (d: z ~> x), f ∘ d = g ∘ d -> exists! u: z ~> E, e ∘ u = d.

Definition is_eq_obj {C: Category} {x y: C} (f g: x ~> y) (E: C) :=
  exists e, is_equalizer f g E e.

Definition ex_equalizer {C: Category} {x y: C} (f g: x ~> y) :=
  exists E, is_eq_obj f g E.

Instance is_eq_obj_iso {C: Category} {x y: C} (f g: x ~> y): Proper (isomorphic C ==> iff) (is_eq_obj f g).
Proof.
  enough (Proper (isomorphic C ==> impl) (is_eq_obj f g)).
  now split; apply H.
  intros E E' [i] [e [He H]].
  exists (e ∘ i⁻¹).
  split.
  rewrite !comp_assoc.
  now f_equal.
  intros z d Hd.
  specialize (H z d Hd).
  destruct H as [u [Hu H]].
  subst d.
  exists (i ∘ u).
  split.
  rewrite comp_assoc, <- (comp_assoc e).
  f_equal.
  rewrite inv_l.
  apply comp_id_r.
  intros u' Hu'.
  apply (iso_monic i⁻¹).
  rewrite comp_assoc, inv_l, comp_id_l.
  apply H.
  now rewrite comp_assoc.
Qed.

Lemma iso_eq_obj {C: Category} (x y: C) (f g: x ~> y) (E E': C): is_eq_obj f g E -> is_eq_obj f g E' -> E ≃ E'.
Proof.
  intros [e [He H]] [e' [He' H0]].
  destruct (H0 E e He) as [to [H1 _]].
  destruct (H E' e' He') as [from [H2 _]].
  constructor.
  exists to, from.
  + specialize (H E e He).
    destruct H as [u [_ Hu]].
    transitivity u.
    symmetry.
    all: apply Hu.
    rewrite comp_assoc, H2.
    apply H1.
    apply comp_id_r.
  + specialize (H0 E' e' He').
    destruct H0 as [u [_ Hu]].
    transitivity u.
    symmetry.
    all: apply Hu.
    rewrite comp_assoc, H1.
    apply H2.
    apply comp_id_r.
Qed.

Module EqCategory.

Structure mixin_of (C: Category) := Mixin {
  Eqz {x y: C} (f g: x ~> y): C;
  eqz {x y: C} (f g: x ~> y): Eqz f g ~> x;
  eqz_comm {x y: C} (f g: x ~> y): f ∘ eqz f g = g ∘ eqz f g;
  eqz_med {x y z: C} (f g: y ~> z) (e: x ~> y): f ∘ e = g ∘ e -> x ~> Eqz f g;
  eqz_med_comm {x y z: C} (f g: y ~> z) (e: x ~> y) (H: f ∘ e = g ∘ e): eqz f g ∘ (eqz_med f g e H) = e;
  eqz_med_unique {x y z: C} (f g: y ~> z) (e: x ~> y) (u: x ~> Eqz f g) (H: f ∘ e = g ∘ e): eqz f g ∘ u = e -> eqz_med f g e H = u;
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
Notation EqCategory := type.

End Exports.

End EqCategory.

Export EqCategory.Exports.

Section Equalizer.
Context {C: EqCategory}.

Definition Eqz: forall {x y: C} (f g: x ~> y), C := @EqCategory.Eqz C (EqCategory.class C).
Definition eqz: forall {x y: C} (f g: x ~> y), Eqz f g ~> x := @EqCategory.eqz C (EqCategory.class C).
Definition eqz_med: forall {x y z: C} (f g: y ~> z) (e: x ~> y), f ∘ e = g ∘ e -> x ~> Eqz f g := @EqCategory.eqz_med C (EqCategory.class C).

Lemma eqz_comm {x y: C} (f g: x ~> y): f ∘ eqz f g = g ∘ eqz f g.
Proof. apply EqCategory.eqz_comm. Qed.
Lemma eqz_med_comm {x y z: C} (f g: y ~> z) (e: x ~> y) (H: f ∘ e = g ∘ e): eqz f g ∘ (eqz_med f g e H) = e.
Proof. apply EqCategory.eqz_med_comm. Qed.
Lemma eqz_med_unique {x y z: C} (f g: y ~> z) (e: x ~> y) (u: x ~> Eqz f g) (H: f ∘ e = g ∘ e): eqz f g ∘ u = e -> eqz_med f g e H = u.
Proof. apply EqCategory.eqz_med_unique. Qed.

End Equalizer.
