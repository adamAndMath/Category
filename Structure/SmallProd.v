Require Export Base.

Module SProdCategory.

Structure mixin_of (C: Category) := Mixin {
  sprod {I}: (I -> C) -> C;
  sfork {I} {X: C} {F: I -> C}: (forall i, X ~> F i) -> X ~> sprod F;
  pi {I} {F: I -> C} (i: I): sprod F ~> F i;
  sfork_ump {I} {X: C} {F: I -> C} (f: forall i, X ~> F i) (g: X ~> sprod F): sfork f = g <-> forall i, pi i ∘ g = f i;
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
Notation SProdCategory := type.

End Exports.
End SProdCategory.

Export SProdCategory.Exports.

Section SProdCategory_theory.
Context {C: SProdCategory}.

Definition sprod: forall {I}, (I -> C) -> C := @SProdCategory.sprod C (SProdCategory.class C).
Definition sfork: forall {I} {X: C} {F: I -> C}, (forall i, X ~> F i) -> X ~> sprod F := @SProdCategory.sfork C (SProdCategory.class C).
Definition pi: forall {I} {F: I -> C} (i: I), sprod F ~> F i := @SProdCategory.pi C (SProdCategory.class C).
Definition sfork_ump: forall {I} {X: C} {F: I -> C} (f: forall i, X ~> F i) (g: X ~> sprod F), sfork f = g <-> forall i, pi i ∘ g = f i := @SProdCategory.sfork_ump C (SProdCategory.class C).

Notation "∏ i .. j , x" := (sprod (fun i => .. (sprod (fun j => x)) ..)) (at level 40, i binder).
Notation "∏' i .. j , f" := (sfork (fun i => .. (sfork (fun j => f)) ..)) (at level 40, i binder).
Notation π := pi.

Lemma to_sprod_eq {I} {F: I -> C} {X: C} (f g: X ~> sprod F): f = g <-> forall i, π i ∘ f = π i ∘ g.
Proof.
  split.
  now intros [].
  intros H.
  transitivity (∏' i, (π i ∘ g)).
  symmetry.
  all: now apply sfork_ump.
Qed.

Definition spmap {I} {F G: I -> C} (η: forall i, F i ~> G i): sprod F ~> sprod G :=
  ∏' i, (η i ∘ π i).

Notation "(∏) i .. j , f" := (spmap (fun i => .. (spmap (fun j => f)) ..)) (at level 40, i binder).

Lemma pi_sfork {I} {F: I -> C} {X: C} (η: forall i, X ~> F i) (i: I): π i ∘ sfork η = η i.
Proof. now apply sfork_ump. Qed.

Lemma pi_spmap {I} {F G: I -> C} (η: forall i, F i ~> G i) (i: I): π i ∘ spmap η = η i ∘ π i.
Proof. exact (pi_sfork (fun i => η i ∘ π i) i). Qed.

Lemma spmap_id {I} {F: I -> C}: (∏) i, id (F i) = id (sprod F).
Proof.
  apply to_sprod_eq.
  intros i.
  rewrite pi_spmap.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Lemma spmap_comp {I} {F G H: I -> C} (η: forall i, G i ~> H i) (ϵ: forall i, F i ~> G i): (∏) i, (η i ∘ ϵ i) = spmap η ∘ spmap ϵ.
Proof.
  apply to_sprod_eq.
  intros i.
  rewrite comp_assoc.
  rewrite !pi_spmap.
  rewrite <- !comp_assoc.
  f_equal.
  symmetry.
  apply pi_spmap.
Qed.

End SProdCategory_theory.

Notation "∏ i .. j , x" := (sprod (fun i => .. (sprod (fun j => x)) ..)) (at level 40, i binder).
Notation "∏' i .. j , f" := (sfork (fun i => .. (sfork (fun j => f)) ..)) (at level 40, i binder).
Notation π := pi.
Notation "(∏) i .. j , f" := (spmap (fun i => .. (spmap (fun j => f)) ..)) (at level 40, i binder).
