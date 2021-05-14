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

Definition scpmap {I} {F G: I -> C} (η: forall i, F i ~> G i): scoprod F ~> scoprod G :=
  ∑' i, (ι i ∘ η i).

Notation "(∑) i .. j , f" := (scpmap (fun i => .. (scpmap (fun j => f)) ..)) (at level 40, i binder).

Lemma smerge_sinto {I} {F: I -> C} {X: C} (η: forall i, F i ~> X) (i: I): smerge η ∘ ι i = η i.
Proof. now apply smerge_ump. Qed.

Lemma scpmap_sinto {I} {F G: I -> C} (η: forall i, F i ~> G i) (i: I): scpmap η ∘ ι i = ι i ∘ η i.
Proof. exact (smerge_sinto (fun i => ι i ∘ η i) i). Qed.

Lemma comp_smerge {I} {F: I -> C} {X Y: C} (f: X ~> Y) (g: forall i, F i ~> X): ∑' i, (f ∘ g i) = f ∘ smerge g.
Proof.
  apply from_scoprod_eq.
  intros i.
  rewrite <- comp_assoc.
  now rewrite !smerge_sinto.
Qed.

Lemma smerge_scpmap {I} {F G: I -> C} {X: C} (f: forall i, G i ~> X) (g: forall i, F i ~> G i): smerge f ∘ scpmap g = ∑' i, (f i ∘ g i).
Proof.
  apply from_scoprod_eq.
  intros i.
  rewrite <- comp_assoc.
  rewrite scpmap_sinto.
  rewrite comp_assoc.
  now rewrite !smerge_sinto.
Qed.

Lemma scpmap_id {I} (F: I -> C): (∑) i, id (F i) = id (scoprod F).
Proof.
  apply from_scoprod_eq.
  intros i.
  rewrite scpmap_sinto.
  rewrite comp_id_l.
  apply comp_id_r.
Qed.

Lemma scpmap_comp {I} {F G H: I -> C} (η: forall i, G i ~> H i) (ϵ: forall i, F i ~> G i): (∑) i, (η i ∘ ϵ i) = scpmap η ∘ scpmap ϵ.
Proof.
  apply from_scoprod_eq.
  intros i.
  rewrite <- comp_assoc.
  rewrite !scpmap_sinto.
  rewrite !comp_assoc.
  f_equal.
  symmetry.
  apply scpmap_sinto.
Qed.

End SCoprodCategory_theory.

Notation "∑ i .. j , x" := (scoprod (fun i => .. (scoprod (fun j => x)) ..)) (at level 40, i binder).
Notation "∑' i .. j , f" := (smerge (fun i => .. (smerge (fun j => f)) ..)) (at level 40, i binder).
Notation ι := sinto.
Notation "(∑) i .. j , f" := (scpmap (fun i => .. (scpmap (fun j => f)) ..)) (at level 40, i binder).

Instance smerge_pw C I X F: Proper (forall_relation (fun _ => eq) ==> eq) (@smerge C I X F).
Proof.
  intros f g H.
  f_equal.
  now extensionality i.
Qed.

Instance scpmap_pw C I F G: Proper (forall_relation (fun _ => eq) ==> eq) (@scpmap C I F G).
Proof.
  intros f g H.
  f_equal.
  now extensionality i.
Qed.
