Require Export Base.

Module SCoprodCategory.

Structure mixin_of (C: Category) := Mixin {
  scoprod {I}: (I -> C) -> C;
  smerge {I} {X: C} {F: I -> C}: (forall i, F i ~> X) -> scoprod F ~> X;
  sinto {I} {F: I -> C} (i: I): F i ~> scoprod F;
  smerge_ump {I} {X: C} {F: I -> C} (f: forall i, F i ~> X) (g: scoprod F ~> X): smerge f = g <-> forall i, g ∘ sinto i = f i;
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
Notation SCoprodCategory := type.

End Exports.
End SCoprodCategory.

Export SCoprodCategory.Exports.

Section SCoprodCategory_theory.
Context {C: SCoprodCategory}.

Definition scoprod: forall {I}, (I -> C) -> C := @SCoprodCategory.scoprod C (SCoprodCategory.class C).
Definition smerge: forall {I} {X: C} {F: I -> C}, (forall i, F i ~> X) -> scoprod F ~> X := @SCoprodCategory.smerge C (SCoprodCategory.class C).
Definition sinto: forall {I} {F: I -> C} (i: I), F i ~> scoprod F := @SCoprodCategory.sinto C (SCoprodCategory.class C).
Definition smerge_ump: forall {I} {X: C} {F: I -> C} (f: forall i, F i ~> X) (g: scoprod F ~> X), smerge f = g <-> forall i, g ∘ sinto i = f i := @SCoprodCategory.smerge_ump C (SCoprodCategory.class C).

Notation "∑ i .. j , x" := (scoprod (fun i => .. (scoprod (fun j => x)) ..)) (at level 40, i binder).
Notation "∑' i .. j , f" := (smerge (fun i => .. (smerge (fun j => f)) ..)) (at level 40, i binder).
Notation ι := sinto.

Lemma from_scoprod_eq {I} {F: I -> C} {X: C} (f g: scoprod F ~> X): f = g <-> forall i, f ∘ ι i = g ∘ ι i.
Proof.
  split.
  now intros [].
  intros H.
  transitivity (∑' i, (g ∘ ι i)).
  symmetry.
  all: now apply smerge_ump.
Qed.

Definition spmap {I} {F G: I -> C} (η: forall i, F i ~> G i): scoprod F ~> scoprod G :=
  ∑' i, (ι i ∘ η i).

Notation "(∑) i .. j , f" := (spmap (fun i => .. (spmap (fun j => f)) ..)) (at level 40, i binder).

Lemma smerge_sinto {I} {F: I -> C} {X: C} (η: forall i, F i ~> X) (i: I): smerge η ∘ ι i = η i.
Proof. now apply smerge_ump. Qed.

Lemma spmap_sinto {I} {F G: I -> C} (η: forall i, F i ~> G i) (i: I): spmap η ∘ ι i = ι i ∘ η i.
Proof. exact (smerge_sinto (fun i => ι i ∘ η i) i). Qed.

Lemma spmap_id {I} {F: I -> C}: (∑) i, id (F i) = id (scoprod F).
Proof.
  apply from_scoprod_eq.
  intros i.
  rewrite spmap_sinto.
  rewrite comp_id_l.
  apply comp_id_r.
Qed.

Lemma spmap_comp {I} {F G H: I -> C} (η: forall i, G i ~> H i) (ϵ: forall i, F i ~> G i): (∑) i, (η i ∘ ϵ i) = spmap η ∘ spmap ϵ.
Proof.
  apply from_scoprod_eq.
  intros i.
  rewrite <- comp_assoc.
  rewrite !spmap_sinto.
  rewrite !comp_assoc.
  f_equal.
  symmetry.
  apply spmap_sinto.
Qed.

End SCoprodCategory_theory.

Notation "∑ i .. j , x" := (scoprod (fun i => .. (scoprod (fun j => x)) ..)) (at level 40, i binder).
Notation "∑' i .. j , f" := (smerge (fun i => .. (smerge (fun j => f)) ..)) (at level 40, i binder).
Notation ι := sinto.
Notation "(∑) i .. j , f" := (spmap (fun i => .. (spmap (fun j => f)) ..)) (at level 40, i binder).
