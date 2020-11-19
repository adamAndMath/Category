Require Export Categories.Parallel.
Require Export Categories.Poset.
Require Export Categories.Slice.
Require Export Limit.
Require Export Limits.Product.
Require Export Limits.Coproduct.

Section ex1.
Universes i.
Context {T: Type@{i}}.

Lemma poset_equalizer (R: T -> T -> Prop) {pre: PreOrder R} (po: PartialOrder eq R): has_limit Parallel (Poset@{i Set} R).
Proof.
  intros F.
  unshelve eexists.
  unshelve econstructor.
  exact (F false).
  intros [].
  exact (fmap F (Parallel.arr false)).
  exact (id (F false)).
  intros x y f.
  apply Proset.hom_eq.
  intros N.
  unshelve eexists.
  exists (Cone.edge N false).
  simpl.
  intros x.
  apply Proset.hom_eq.
  intros [f Hf].
  simpl in f, Hf.
  Cone.hom_eq.
  apply Proset.hom_eq.
Qed.

Lemma poset_coequalizer@{j} (R: T -> T -> Prop) {pre: PreOrder R} (po: PartialOrder eq R): has_colimit@{Set Set i Set j} Parallel (Poset@{i Set} R).
Proof.
  rewrite <- (co_invol Parallel), <- co_invol.
  apply (has_limit_co@{Set Set i Set j}).
  rewrite dual_poset.
  generalize (@poset_equalizer (flip R) _ (PartialOrder_inverse po)).
  apply has_limit_iso.
  symmetry.
  exact Parallel.dual_iso.
  reflexivity.
Qed.

End ex1.

Section ex2.

Lemma iso_prod (C D: Category): C ≃ D -> inhabited (ProdCategory.mixin_of C) <-> inhabited (ProdCategory.mixin_of D).
Proof.
  intros H.
  rewrite <- !prod_limit.
  f_equiv.
  apply iso_cequiv, H.
Qed.

Lemma iso_coprod (C D: Category): C ≃ D -> inhabited (CoprodCategory.mixin_of C) <-> inhabited (CoprodCategory.mixin_of D).
Proof.
  intros H.
  rewrite <- !coprod_limit.
  rewrite <- !ex_lim_co.
  do 2 f_equiv.
  apply iso_cequiv, H.
Qed.

Lemma iso_equalizer (C D: Category): C ≃ D -> has_limit Parallel C <-> has_limit Parallel D.
Proof.
  intros H.
  f_equiv.
  apply iso_cequiv, H.
Qed.

Lemma iso_coequalizer (C D: Category): C ≃ D -> has_colimit Parallel C <-> has_colimit Parallel D.
Proof.
  intros H.
  rewrite Parallel.dual_iso.
  rewrite <- (co_invol C), <- (co_invol D).
  rewrite <- !has_limit_co.
  f_equiv.
  apply iso_cequiv.
  apply co_iso, H.
Qed.

End ex2.

Section ex3_1.
Context (C: Category) (X: C).

Definition slice_one: C / X := {|
  Slice.dom := X;
  Slice.oarr := id X;
|}.

Definition slice_to_one (a: C / X): a ~> slice_one := {|
  Slice.arr := Slice.oarr a: Slice.dom a ~> Slice.dom slice_one;
  Slice.comm := comp_id_l (Slice.oarr a);
|}.

Lemma slice_to_one_unique (a: C / X) (f: a ~> slice_one): slice_to_one a = f.
Proof.
  apply Slice.hom_eq; simpl.
  specialize (Slice.comm f) as H.
  simpl in H.
  rewrite comp_id_l in H.
  now symmetry.
Qed.

Definition TopSlice_mixin: TopCategory.mixin_of (C / X) :=
  TopCategory.Mixin (C / X) slice_one slice_to_one slice_to_one_unique.

Definition TopSlice: TopCategory :=
  TopCategory.Pack (C / X) TopSlice_mixin.

End ex3_1.

Section ex3_2.
Context (C: BotCategory) (X: C).

Definition slice_zero: C / X := {|
  Slice.dom := 0;
  Slice.oarr := ¡;
|}.

Definition slice_from_zero (a: C / X): slice_zero ~> a := {|
  Slice.arr := ¡: Slice.dom slice_zero ~> Slice.dom a;
  Slice.comm := eq_sym (from_zero_unique _);
|}.

Lemma slice_from_zero_unique (a: C / X) (f: slice_zero ~> a): slice_from_zero a = f.
Proof.
  apply Slice.hom_eq; simpl.
  apply from_zero_unique.
Qed.

Definition BotSlice_mixin: BotCategory.mixin_of (C / X) :=
  BotCategory.Mixin (C / X) slice_zero slice_from_zero slice_from_zero_unique.

Definition BotSlice: BotCategory :=
  BotCategory.Pack (C / X) BotSlice_mixin.

End ex3_2.

Section ex3_3.
Context (C: EqCategory) (X: C).

Definition slice_Eqz {x y: C / X} (f g: x ~> y): C / X := {|
  Slice.dom := Eqz (Slice.arr f) (Slice.arr g);
  Slice.oarr := Slice.oarr x ∘ eqz (Slice.arr f) (Slice.arr g);
|}.

Program Definition slice_eqz {x y: C / X} (f g: x ~> y): slice_Eqz f g ~> x := {|
  Slice.arr := eqz (Slice.arr f) (Slice.arr g);
|}.

Program Definition slice_eqz_med {x y z: C / X} (f g: y ~> z) (e: x ~> y) (He: f ∘ e = g ∘ e): x ~> slice_Eqz f g := {|
  Slice.arr := (eqz_med (Slice.arr f) (Slice.arr g) (Slice.arr e)) (proj1 (Slice.hom_eq _ _ _ _) He);
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite eqz_med_comm.
  apply Slice.comm.
Qed.

Lemma slice_eqz_comm {x y: C / X} (f g: x ~> y): f ∘ slice_eqz f g = g ∘ slice_eqz f g.
Proof.
  apply Slice.hom_eq; simpl.
  apply eqz_comm.
Qed.

Lemma slice_eqz_med_comm {x y z: C / X} (f g: y ~> z) (e: x ~> y) (H: f ∘ e = g ∘ e): slice_eqz f g ∘ (slice_eqz_med f g e H) = e.
Proof.
  apply Slice.hom_eq; simpl.
  apply eqz_med_comm.
Qed.

Lemma slice_eqz_med_unique {x y z: C / X} (f g: y ~> z) (e: x ~> y) (u: x ~> slice_Eqz f g) (H: f ∘ e = g ∘ e): slice_eqz f g ∘ u = e -> slice_eqz_med f g e H = u.
Proof.
  intros H'.
  subst e.
  apply Slice.hom_eq; simpl.
  now apply eqz_med_unique.
Qed.

Definition EqSlice_mixin: EqCategory.mixin_of (C / X) :=
  EqCategory.Mixin (C / X) (@slice_Eqz) (@slice_eqz) (@slice_eqz_comm) (@slice_eqz_med) (@slice_eqz_med_comm) (@slice_eqz_med_unique).

Definition EqSlice: EqCategory :=
  EqCategory.Pack (C / X) EqSlice_mixin.
End ex3_3.
