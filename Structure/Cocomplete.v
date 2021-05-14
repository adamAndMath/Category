Require Export Base.

Module Cocomplete.

Structure mixin_of (C: Category) := Mixin {
  colim {D: Category} (F: Functor D C): C;
  Colim {D: Category} (F: Functor D C): F ~> Δ (colim F);
  colim_med {D: Category} {F: Functor D C} {X: C} (η: F ~> Δ X): colim F ~> X;
  colim_med_comm {D: Category} {F: Functor D C} {X: C} (η: F ~> Δ X): ∇ (colim_med η) ∘ Colim F = η;
  colim_med_unique {D: Category} {F: Functor D C} {X: C} (η: F ~> Δ X) (f: colim F ~> X): ∇ f ∘ Colim F = η -> colim_med η = f;
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
Notation Cocomplete := type.

End Exports.
End Cocomplete.

Export Cocomplete.Exports.

Section Cocomplete_theory.
Context {C: Cocomplete}.

Definition colim: forall {D: Category} (F: Functor D C), C := @Cocomplete.colim C (Cocomplete.class C).
Definition Colim: forall {D: Category} (F: Functor D C), F ~> Δ (colim F) := @Cocomplete.Colim C (Cocomplete.class C).
Definition colim_med: forall {D: Category} {F: Functor D C} {X: C} (η: F ~> Δ X), colim F ~> X := @Cocomplete.colim_med C (Cocomplete.class C).
Definition colim_med_comm: forall {D: Category} {F: Functor D C} {X: C} (η: F ~> Δ X), ∇ (colim_med η) ∘ Colim F = η := @Cocomplete.colim_med_comm C (Cocomplete.class C).
Definition colim_med_unique: forall {D: Category} {F: Functor D C} {X: C} (η: F ~> Δ X) (f: colim F ~> X), ∇ f ∘ Colim F = η -> colim_med η = f := @Cocomplete.colim_med_unique C (Cocomplete.class C).

Lemma from_colim_eq {D} {F: Functor D C} {X: C} (f g: colim F ~> X): f = g <-> forall x, f ∘ Colim F x = g ∘ Colim F x.
Proof.
  split.
  now intros [].
  intros H.
  transitivity (colim_med (∇ g ∘ Colim F)).
  symmetry.
  all: apply colim_med_unique.
  2: reflexivity.
  now natural_eq x.
Qed.

Definition Colim_map {D: Category} {F G: Functor D C} (η: F ~> G): colim F ~> colim G :=
  colim_med (Colim G ∘ η).

Lemma Colim_map_comm {D: Category} {F G: Functor D C} (η: F ~> G): ∇ (Colim_map η) ∘ Colim F = Colim G ∘ η.
Proof. apply colim_med_comm. Qed.

Lemma colim_med_Colim {D: Category} {F: Functor D C} {X: C} (η: F ~> Δ X) (Y: D): colim_med η ∘ Colim F Y = η Y.
Proof. exact (proj1 (natural_eq _ _) (colim_med_comm η) Y). Qed.

Lemma Colim_map_Colim {D: Category} {F G: Functor D C} (η: F ~> G) (X: D): Colim_map η ∘ Colim F X = Colim G X ∘ η X.
Proof. exact (proj1 (natural_eq _ _) (Colim_map_comm η) X). Qed.

Lemma Colim_map_id {D: Category} {F: Functor D C}: Colim_map (id F) = id (colim F).
Proof.
  apply from_colim_eq.
  intros x.
  rewrite Colim_map_Colim.
  rewrite comp_id_l.
  apply comp_id_r.
Qed.

Lemma Colim_map_comp {D: Category} {F G H: Functor D C} (η: G ~> H) (ϵ: F ~> G): Colim_map (η ∘ ϵ) = Colim_map η ∘ Colim_map ϵ.
Proof.
  apply from_colim_eq.
  intros x.
  rewrite <- comp_assoc.
  rewrite !Colim_map_Colim; simpl.
  rewrite !comp_assoc.
  f_equal.
  symmetry.
  apply Colim_map_Colim.
Qed.

Canonical FColim {D: Category}: Functor (Fun D C) C := {|
  fobj := colim;
  fmap := @Colim_map D;
  fmap_id := @Colim_map_id D;
  fmap_comp := @Colim_map_comp D;
|}.

Definition map_Colimit {D E: Category} (F: Functor E C) (G: Functor D E): colim (F ∘ G) ~> colim F :=
  colim_med (eq_iso (diag_comp (colim F) G) ∘ (Colim F |> G)).

Lemma map_Colimit_Colim {D E: Category} (F: Functor E C) (G: Functor D E) (X: D): map_Colimit F G ∘ Colim (F ∘ G) X = Colim F (G X).
Proof.
  unfold map_Colimit.
  rewrite colim_med_Colim; simpl.
  rewrite <- comp_id_l.
  apply (f_equal (fun f => f ∘ _)).
  apply is_eq_refl.
  apply (transform_is_eq (eq_iso (diag_comp (colim F) G))).
  apply eq_iso_is_eq.
Qed.

Lemma map_Colimit_map {D E: Category} {F G: Functor E C} (H: Functor D E) (η: F ~> G): map_Colimit G H ∘ Colim_map (η |> H) = Colim_map η ∘ map_Colimit F H.
Proof.
  apply from_colim_eq.
  intros x.
  rewrite <- !comp_assoc.
  rewrite Colim_map_Colim.
  rewrite (map_Colimit_Colim F).
  rewrite comp_assoc.
  rewrite map_Colimit_Colim.
  symmetry.
  exact (Colim_map_Colim η (H x)).
Qed.

Lemma map_Colimit_is_eq {D E: Category} (F: Functor E C) (G: Functor D E): is_eq G -> is_eq (map_Colimit F G).
Proof.
  intros [e H].
  unfold fun_hom in H.
  subst G.
  destruct e; simpl.
  cut (is_eq (Colim_map (ρ F))).
  change (?P -> ?Q) with (impl P Q).
  f_equiv.
  symmetry.
  apply colim_med_unique.
  rewrite Colim_map_comm.
  rewrite <- unitor_whisk_r.
  f_equal.
  apply is_eq_unique.
  apply unitor_r_is_eq.
  apply eq_iso_is_eq.
  apply fmap_is_eq, unitor_r_is_eq.
Qed.

End Cocomplete_theory.
