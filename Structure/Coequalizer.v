Require Export Base.

Definition is_coequalizer {C: Category} {x y: C} (f g: x ~> y) (E: C) (e: y ~> E) :=
  e ∘ f = e ∘ g /\
  forall z (d: y ~> z), d ∘ f = d ∘ g -> exists! u: E ~> z, u ∘ e = d.

Definition is_coeq_obj {C: Category} {x y: C} (f g: x ~> y) (E: C) :=
  exists e, is_coequalizer f g E e.

Definition ex_coequalizer {C: Category} {x y: C} (f g: x ~> y) :=
  exists E, is_coeq_obj f g E.

Instance is_coeq_obj_iso {C: Category} {x y: C} (f g: x ~> y): Proper (isomorphic C ==> iff) (is_coeq_obj f g).
Proof.
  enough (Proper (isomorphic C ==> impl) (is_coeq_obj f g)).
  now split; apply H.
  intros E E' [i] [e [He H]].
  exists (i ∘ e).
  split.
  rewrite <- !comp_assoc.
  now f_equal.
  intros z d Hd.
  specialize (H z d Hd).
  destruct H as [u [Hu H]].
  subst d.
  exists (u ∘ i⁻¹).
  split.
  rewrite comp_assoc, <- (comp_assoc u).
  f_equal.
  rewrite inv_l.
  apply comp_id_r.
  intros u' Hu'.
  apply (iso_epic i).
  rewrite <- comp_assoc, inv_l, comp_id_r.
  apply H.
  now rewrite <- comp_assoc.
Qed.

Lemma iso_eq_obj {C: Category} (x y: C) (f g: x ~> y) (E E': C): is_coeq_obj f g E -> is_coeq_obj f g E' -> E ≃ E'.
Proof.
  intros [e [He H]] [e' [He' H0]].
  destruct (H E' e' He') as [to [H1 _]].
  destruct (H0 E e He) as [from [H2 _]].
  constructor.
  exists to, from.
  + specialize (H E e He).
    destruct H as [u [_ Hu]].
    transitivity u.
    symmetry.
    all: apply Hu.
    rewrite <- comp_assoc, H1.
    apply H2.
    apply comp_id_l.
  + specialize (H0 E' e' He').
    destruct H0 as [u [_ Hu]].
    transitivity u.
    symmetry.
    all: apply Hu.
    rewrite <- comp_assoc, H2.
    apply H1.
    apply comp_id_l.
Qed.

Module CoeqCategory.

Structure mixin_of (C: Category) := Mixin {
  coEqz {x y: C} (f g: x ~> y): C;
  coeqz {x y: C} (f g: x ~> y): y ~> coEqz f g;
  coeqz_comm {x y: C} (f g: x ~> y): coeqz f g ∘ f = coeqz f g ∘ g;
  coeqz_med {x y z: C} (f g: x ~> y) (e: y ~> z): e ∘ f = e ∘ g -> coEqz f g ~> z;
  coeqz_med_comm {x y z: C} (f g: x ~> y) (e: y ~> z) (H: e ∘ f = e ∘ g): (coeqz_med f g e H) ∘ coeqz f g = e;
  coeqz_med_unique {x y z: C} (f g: x ~> y) (e: y ~> z) (u: coEqz f g ~> z) (H: e ∘ f = e ∘ g): u ∘ coeqz f g = e -> coeqz_med f g e H = u;
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
Notation CoeqCategory := type.

End Exports.

End CoeqCategory.

Export CoeqCategory.Exports.

Section Coequalizer.
Context {C: CoeqCategory}.

Definition coEqz: forall {x y: C} (f g: x ~> y), C := @CoeqCategory.coEqz C (CoeqCategory.class C).
Definition coeqz: forall {x y: C} (f g: x ~> y), y ~> coEqz f g := @CoeqCategory.coeqz C (CoeqCategory.class C).
Definition coeqz_med: forall {x y z: C} (f g: x ~> y) (e: y ~> z), e ∘ f = e ∘ g -> coEqz f g ~> z := @CoeqCategory.coeqz_med C (CoeqCategory.class C).

Lemma coeqz_comm {x y: C} (f g: x ~> y): coeqz f g ∘ f = coeqz f g ∘ g.
Proof. apply CoeqCategory.coeqz_comm. Qed.
Lemma coeqz_med_comm {x y z: C} (f g: x ~> y) (e: y ~> z) (H: e ∘ f = e ∘ g): (coeqz_med f g e H) ∘ coeqz f g = e.
Proof. apply CoeqCategory.coeqz_med_comm. Qed.
Lemma coeqz_med_unique {x y z: C} (f g: x ~> y) (e: y ~> z) (u: coEqz f g ~> z) (H: e ∘ f = e ∘ g): u ∘ coeqz f g = e -> coeqz_med f g e H = u.
Proof. apply CoeqCategory.coeqz_med_unique. Qed.

End Coequalizer.
