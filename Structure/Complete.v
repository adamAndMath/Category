Require Export Base.

Module Complete.

Structure mixin_of (C: Category) := Mixin {
  lim {D: Category} (F: Functor D C): C;
  Lim {D: Category} (F: Functor D C): Δ (lim F) ~> F;
  lim_med {D: Category} {F: Functor D C} {X: C} (η: Δ X ~> F): X ~> lim F;
  lim_med_comm {D: Category} {F: Functor D C} {X: C} (η: Δ X ~> F): Lim F ∘ ∇ (lim_med η) = η;
  lim_med_unique {D: Category} {F: Functor D C} {X: C} (η: Δ X ~> F) (f: X ~> lim F): Lim F ∘ ∇ f = η -> lim_med η = f;
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
Notation Complete := type.

End Exports.
End Complete.

Export Complete.Exports.

Section Complete_theory.
Context {C: Complete}.

Definition lim: forall {D: Category} (F: Functor D C), C := @Complete.lim C (Complete.class C).
Definition Lim: forall {D: Category} (F: Functor D C), Δ (lim F) ~> F := @Complete.Lim C (Complete.class C).
Definition lim_med: forall {D: Category} {F: Functor D C} {X: C} (η: Δ X ~> F), X ~> lim F := @Complete.lim_med C (Complete.class C).
Definition lim_med_comm: forall {D: Category} {F: Functor D C} {X: C} (η: Δ X ~> F), Lim F ∘ ∇ (lim_med η) = η := @Complete.lim_med_comm C (Complete.class C).
Definition lim_med_unique: forall {D: Category} {F: Functor D C} {X: C} (η: Δ X ~> F) (f: X ~> lim F), Lim F ∘ ∇ f = η -> lim_med η = f := @Complete.lim_med_unique C (Complete.class C).

Lemma to_lim_eq {D} {F: Functor D C} {X: C} (f g: X ~> lim F): f = g <-> forall x, Lim F x ∘ f = Lim F x ∘ g.
Proof.
  split.
  now intros [].
  intros H.
  transitivity (lim_med (Lim F ∘ ∇ g)).
  symmetry.
  all: apply lim_med_unique.
  2: reflexivity.
  natural_eq x.
  apply H.
Qed.

Definition Lim_map {D: Category} {F G: Functor D C} (η: F ~> G): lim F ~> lim G :=
  lim_med (η ∘ Lim F).

Lemma Lim_map_comm {D: Category} {F G: Functor D C} (η: F ~> G): Lim G ∘ ∇ (Lim_map η) = η ∘ Lim F.
Proof. apply lim_med_comm. Qed.

Lemma Lim_lim_med {D: Category} {F: Functor D C} {X: C} (η: Δ X ~> F) (Y: D): Lim F Y ∘ lim_med η = η Y.
Proof. exact (proj1 (natural_eq _ _) (lim_med_comm η) Y). Qed.

Lemma Lim_Lim_map {D: Category} {F G: Functor D C} (η: F ~> G) (X: D): Lim G X ∘ Lim_map η = η X ∘ Lim F X.
Proof. exact (proj1 (natural_eq _ _) (Lim_map_comm η) X). Qed.

Lemma Lim_map_id {D: Category} {F: Functor D C}: Lim_map (id F) = id (lim F).
Proof.
  apply to_lim_eq.
  intros x.
  rewrite Lim_Lim_map.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Lemma Lim_map_comp {D: Category} {F G H: Functor D C} (η: G ~> H) (ϵ: F ~> G): Lim_map (η ∘ ϵ) = Lim_map η ∘ Lim_map ϵ.
Proof.
  apply to_lim_eq.
  intros x.
  rewrite comp_assoc.
  rewrite !Lim_Lim_map; simpl.
  rewrite <- !comp_assoc.
  f_equal.
  symmetry.
  apply Lim_Lim_map.
Qed.

Canonical FLim {D: Category}: Functor (Fun D C) C := {|
  fobj := lim;
  fmap := @Lim_map D;
  fmap_id := @Lim_map_id D;
  fmap_comp := @Lim_map_comp D;
|}.

Definition map_Limit {D E: Category} (F: Functor E C) (G: Functor D E): lim F ~> lim (F ∘ G) :=
  lim_med ((Lim F |> G) ∘ (eq_iso (diag_comp (lim F) G))⁻¹).

Lemma Lim_map_Limit {D E: Category} (F: Functor E C) (G: Functor D E) (X: D): Lim (F ∘ G) X ∘ map_Limit F G = Lim F (G X).
Proof.
  unfold map_Limit.
  rewrite Lim_lim_med; simpl.
  rewrite <- comp_id_r.
  f_equal.
  apply is_eq_refl.
  apply (transform_is_eq (eq_iso (diag_comp (lim F) G))⁻¹).
  apply is_eq_inv, eq_iso_is_eq.
Qed.

Lemma map_Limit_map {D E: Category} {F G: Functor E C} (H: Functor D E) (η: F ~> G): Lim_map (η |> H) ∘ map_Limit F H = map_Limit G H ∘ Lim_map η.
Proof.
  apply to_lim_eq.
  intros x.
  rewrite !comp_assoc.
  rewrite Lim_Lim_map.
  rewrite (Lim_map_Limit G).
  rewrite <- comp_assoc.
  setoid_rewrite (Lim_map_Limit F H x).
  symmetry.
  exact (Lim_Lim_map η (H x)).
Qed.

Lemma map_Limit_is_eq {D E: Category} (F: Functor E C) (G: Functor D E): is_eq G -> is_eq (map_Limit F G).
Proof.
  intros [e H].
  unfold fun_hom in H.
  subst G.
  destruct e; simpl.
  cut (is_eq (Lim_map (ρ F)⁻¹)).
  change (?P -> ?Q) with (impl P Q).
  f_equiv.
  symmetry.
  apply lim_med_unique.
  rewrite Lim_map_comm.
  rewrite <- (comp_id_r (Lim F)) at 1.
  rewrite <- (inv_r (ρ (Δ (lim F)))).
  rewrite (comp_assoc (Lim F)).
  rewrite <- unitor_whisk_r.
  rewrite !comp_assoc.
  rewrite inv_l, comp_id_l.
  f_equal.
  apply is_eq_unique.
  apply is_eq_inv, unitor_r_is_eq.
  apply is_eq_inv, eq_iso_is_eq.
  apply fmap_is_eq, is_eq_inv, unitor_r_is_eq.
Qed.

End Complete_theory.
