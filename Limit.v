Require Export Cone Parallel.

Definition is_limit {C D: Category} (F: D ~> C) (L: Cone F) :=
  forall N: Cone F, exists f: N ~> L, forall f', f = f'.

Instance is_limit_iso {C D: Category} (F: D ~> C): Proper (isomorphic _ ==> iff) (is_limit F).
Proof.
  enough (Proper (isomorphic _ ==> impl) (is_limit F)).
  now split; apply H.
  intros X Y [i].
  intros Hx N.
  specialize (Hx N).
  destruct Hx as [f Hf].
  exists (i ∘ f).
  intros g.
  rewrite (Hf (i⁻¹ ∘ g)).
  rewrite comp_assoc, inv_r.
  apply comp_id_l.
Qed.

Definition limit_ex {C D: Category} (F: D ~> C) :=
  exists L, is_limit F L.

Lemma limit_ex_alt {C D: Category} (F: D ~> C): limit_ex F <-> exists l (η: Δ l ~> F), forall n (ϵ: Δ n ~> F), exists! f: n ~> l, η ∘ fmap Δ f = ϵ.
Proof.
  split.
  + intros [L H].
    exists (vertex L).
    exists (nat_cone L).
    intros n η.
    specialize (H (cone_nat n η)).
    destruct H as [f H].
    exists f.
    split.
    natural_eq x.
    apply (mediator_comm f).
    intros f' H1.
    change (vertex (cone_nat n η) ~> vertex L) in f'.
    specialize (proj1 (natural_eq _ _) H1) as H0.
    simpl in H0.
    clear H1.
    specialize (H {| mediator := f'; mediator_comm := H0 |}).
    now apply conemor_eq in H.
  + intros [l [η H]].
    exists (cone_nat l η).
    intros N.
    specialize (H (vertex N) (nat_cone N)).
    destruct H as [f [H1 H]].
    change (vertex N ~> vertex (cone_nat l η)) in f.
    specialize (proj1 (natural_eq _ _) H1) as Hf.
    simpl in Hf.
    clear H1.
    exists {| mediator := f; mediator_comm := Hf |}.
    intros f'.
    apply conemor_eq; simpl.
    apply H.
    natural_eq x.
    apply (mediator_comm f').
Qed.

Instance limit_ex_iso {C D: Category}: Proper (isomorphic (Fun C D) ==> iff) limit_ex.
Proof.
  enough (Proper (isomorphic (Fun C D) ==> impl) limit_ex).
  now split; apply H.
  intros F G [I].
  rewrite !limit_ex_alt.
  intros [l [η H]].
  exists l, (I ∘ η).
  intros n ϵ.
  specialize (H n (I⁻¹ ∘ ϵ)).
  destruct H as [f [Hf H]].
  exists f.
  split; simpl.
  + rewrite <- comp_assoc.
    etransitivity.
    apply f_equal.
    exact Hf.
    rewrite comp_assoc.
    rewrite inv_r.
    apply comp_id_l.
  + intros f' Hf'.
    apply H.
    rewrite <- Hf'.
    rewrite <- comp_assoc.
    rewrite comp_assoc.
    rewrite inv_l.
    symmetry.
    apply comp_id_l.
Qed.

Definition has_limit (D C: Category) :=
  forall F: D ~> C, limit_ex F.

Definition is_colimit {C D: Category} (F: D ~> C) := is_limit (cof F).

Instance is_colimit_iso {C D: Category} (F: D ~> C): Proper (isomorphic _ ==> iff) (is_limit F).
Proof. apply is_limit_iso. Qed.

Definition has_colimit (D C: Category) :=
  forall F: D ~> C, exists L: Cone (cof F), is_colimit F L.

Lemma is_limit_co {D C: Category} (F: D ~> C) (L: Cone (cof F)): is_limit (cof F) L <-> is_colimit F L.
Proof. reflexivity. Qed.

Lemma has_limit_co (D C: Category): has_limit (co D) (co C) <-> has_colimit D C.
Proof.
  split.
  all: intros H F.
  apply H.
  specialize (H (cof' F)).
  unfold is_colimit in H.
  rewrite cof_inv_r in H.
  exact H.
Qed.

Lemma parallel_limit_ex_co {C: Category} (F: co Parallel ~> C): limit_ex F <-> limit_ex (F ∘ Parallel.dual).
Proof.
  rewrite !limit_ex_alt.
  split.
  + intros [l [η H]].
    exists l, ((η |> Parallel.dual) ∘ (eq_iso (diag_comp l _))⁻¹).
    intros n ϵ.
    specialize (H n (ρ F ∘ (F <| eq_iso (inv_r Parallel.dual)) ∘ (α F _ _)⁻¹ ∘ ((ϵ ∘ (eq_iso (diag_comp n Parallel.dual))) |> Parallel.dual⁻¹) ∘ α (Δ n) _ _ ∘ (Δ n <| (eq_iso (inv_r Parallel.dual))⁻¹) ∘ (ρ (Δ n))⁻¹)).
    destruct H as [u Hu].
    exists u.
    split; [apply proj1 in Hu | apply proj2 in Hu].
    - natural_eq b.
      specialize (proj1 (natural_eq _ _) Hu (negb b)).
      clear Hu; intro Hu.
      unfold comp in Hu; simpl in Hu.
      repeat change (from ?i) with (to i⁻¹) in Hu.
      rewrite (is_eq_refl (to (ρ F) _)) in Hu.
      change (@ρ (co Parallel) C _) with (@ρ (co Parallel) C (Δ n)) in Hu.
      rewrite (is_eq_refl (to (ρ (@Δ C (co Parallel) n))⁻¹ _)) in Hu.
      rewrite (is_eq_refl (to (α (Δ n) Parallel.dual_to Parallel.dual⁻¹) _)) in Hu.
      rewrite (is_eq_refl (to (α F Parallel.dual_to Parallel.dual⁻¹)⁻¹ _)) in Hu.
      destruct b; simpl in Hu |- *.
      rewrite !comp_id_r in Hu.  
      setoid_rewrite comp_id_l in Hu.
      rewrite (Bool.negb_involutive b) in Hu.
      destruct b; simpl in *.
      all: change (Δ l ~> F) in η.
      all: change (Δ n ~> F ∘ Parallel.dual) in ϵ.
      all: change (from ?i) with (to i⁻¹) in *.
      rewrite (is_eq_refl (to (ρ F) false)) in Hu.
      rewrite (is_eq_refl (fmap F (to (eq_iso (inv_r Parallel.dual)) false))) in Hu.
      rewrite comp_id_l in Hu.
      simpl in Hu.
      simpl.

      simpl in Hu.

Lemma parallel_limit_co {C: Category} (F: co Parallel ~> C) (l: C) (η: Δ l ~> F): is_limit F (cone_nat l η) <-> is_limit (F ∘ Parallel.dual) (cone_nat l (eq__)).

Definition is_lim {D C: Category} (F: Fun D C ~> C) := Δ -| F.
Definition ex_lim (D C: Category) := exists F: Fun D C ~> C, is_lim F.

Lemma ex_lim_correct (D C: Category): ex_lim D C -> has_limit D C.
Proof.
  intros [L [ɛ [η adj]]] F.
  apply adjoint_by_alt in adj.
  destruct adj as [adj1 adj2].
  apply limit_ex_alt.
  exists (L F), (ɛ F).
  intros n ϵ.
  exists (fmap L ϵ ∘ η n).
  split.
  + rewrite fmap_comp, comp_assoc.
    change (ɛ F ∘ fmap (Δ ∘ L) ϵ ∘ fmap Δ (η n) = ϵ).
    rewrite naturality.
    simpl fmap at 1.
    rewrite <- comp_assoc.
    rewrite adj1.
    apply comp_id_r.
  + intros f Hf.
    subst ϵ.
    rewrite fmap_comp.
    change (fmap L (ɛ F) ∘ fmap (L ∘ Δ) f ∘ η n = f).
    rewrite <- comp_assoc.
    setoid_rewrite <- (naturality η f).
    rewrite comp_assoc.
    rewrite adj2.
    apply comp_id_l.
Qed.

(*Instance ex_lim_iso: Proper (isomorphic Cat ==> isomorphic Cat ==> iff) ex_lim.
Proof.
  enough (Proper (isomorphic Cat ==> isomorphic Cat ==> impl) ex_lim).
  now split; apply H.
  intros C D I S T J.
  assert (Fun C S ≃ Fun D T).
    now f_equiv.
  clear I.
  destruct H as [I], J as [J].
  intros [L HL].
  exists (J ∘ L ∘ I⁻¹).
  red in HL |- *.
  rewrite <- (comp_id_l Δ), <- (inv_r I).
  rewrite <- comp_assoc.
  apply adjoint_comp, iso_adjoint.
  rewrite <- (comp_id_r (I⁻¹ ∘ Δ)), <- (inv_r J).
  rewrite comp_assoc.
  apply adjoint_comp.
  apply iso_adjoint.
  assert (I⁻¹ ∘ Δ ∘ J ≃ Δ).
    clear.
    apply fun_iso.
    simpl.
    change {| fobj (_: D) := ?x |} with (@Δ _ D x).
    change {| fobj (_: C) := ?x |} with (@Δ _ C x).
    fun_eq F G η.

  intros [L [ɛ [η adj]]].
  exists (J ∘ L ∘ I⁻¹).
  exists (ɛ).
  red.
  rewrite <- comp_assoc.
  rewrite (diag_comp _ J).
  transitivity (ex_lim D S).
  1: clear T J; destruct I as [I].
  2: clear C I; destruct J as [I].
  + intros [L HL].
    red.
    unfold is_lim in HL |- *.
    unshelve eexists.
    eapply comp.
    exact L.
    exists (fun F => F ∘ I) (fun _ _ η => η |> I).
    all: simpl.
    intros F.
    apply whisk_id_r.
    intros F G H ϵ η.
    apply whisk_comp_distr_r.
    intro.
    exact (η |> I).
Qed.

Instance has_limit_iso: Proper (isomorphic Cat ==> isomorphic Cat ==> iff) has_limit.
Proof.
  enough (Proper (isomorphic Cat ==> isomorphic Cat ==> impl) has_limit).
  now split; apply H.
  intros C D I S T J.
  transitivity (has_limit D S).
  1: clear T J; destruct I as [I].
  2: clear C I; destruct J as [I].
  + intros H F.
    specialize (H (F ∘ I)).
    apply limit_ex_alt in H.
    apply limit_ex_alt.
    destruct H as [l [η H]].
    exists l, (ρ F ∘ (F <| eq_iso (inv_r I)) ∘ (α F I I⁻¹)⁻¹ ∘ ((η ∘ eq_iso (diag_comp l I)) |> I⁻¹) ∘ α (Δ l) I I⁻¹ ∘ (Δ l <| (eq_iso (inv_r I))⁻¹) ∘ (ρ (Δ l))⁻¹).
    intros n ϵ.
    specialize (H n ((ϵ |> I) ∘ (eq_iso (diag_comp n I))⁻¹)).
    destruct H as [f [Hf H]].
    exists f.
    split.
    - intros x.
      specialize (Hf (to I⁻¹ x)).
      apply (f_equal (fun f => ((F <| (eq_iso (inv_r I))) ∘ (α F I I⁻¹)⁻¹) x ∘ f)) in Hf.
      change ((F <| eq_iso (inv_r I) ∘ (α F I I ⁻¹) ⁻¹) ∘ ((η |> I⁻¹)) x ∘ f = ((F <| eq_iso (inv_r I) ∘ (α F I I ⁻¹) ⁻¹) ∘ (((ϵ |> I) ∘ (eq_iso (diag_comp n I)) ⁻¹) |> I⁻¹)) x) in Hf.
      rewrite whisk_comp_distr_r in Hf.
      Check (((eq_iso (diag_comp n I))⁻¹ |> I⁻¹)).
      Check (Δ n <| eq_iso (inv_r I)).
      replace ((eq_iso (diag_comp n I))⁻¹ |> I⁻¹) with (Δ n <| eq_iso (inv_r I)).
      simpl in Hf, H |- *.
      change ({| fobj (_ : D) := l |}) with (@Δ _ D l).
      repeat change (from ?i) with (to i⁻¹) in *.
      rewrite comp_id_r.

      fold (@diagonal _ D l).
    split.

    exists (ρ F ∘ (F <| ɛ) ∘ (α F I I⁻¹)⁻¹ ∘ (π |> I⁻¹) ∘ (eq_iso (diag_comp l I⁻¹))⁻¹).
    intros n ϵ.
    specialize (H n ((ϵ |> I) ∘ (eq_iso (diag_comp n I))⁻¹)).
    destruct H as [f [Hf H]].
    exists f.
    simpl in Hf, H |- *.
    repeat change (from ?i) with (to i⁻¹) in *.
    split.
    - intros x.
      specialize (Hf (to I⁻¹ x)).
      rewrite (is_eq_refl (to (α F I I ⁻¹) ⁻¹ x)), comp_id_r.
      rewrite (is_eq_refl (to (ρ F) x)), comp_id_l.
      etransitivity.
      apply (f_equal (fun f => _ ∘ f ∘ _)).
      apply is_eq_refl.
      apply (transform_is_eq (eq_iso (diag_comp l I⁻¹))⁻¹).
      apply is_eq_inv, eq_iso_is_eq.
      rewrite comp_id_r.
      rewrite <- comp_assoc.
      rewrite Hf.
      rewrite (is_eq_refl (to (eq_iso (diag_comp l I⁻¹))⁻¹ x)).
    rewrite <- (naturality η).

    (*assert (e: F ∘ I ∘ I⁻¹ = F).
      rewrite <- comp_assoc.
      rewrite inv_r.
      apply comp_id_r.*)
    exists (eq_iso e ∘ ext η I⁻¹ ∘ (eq_iso (diag_comp l I⁻¹))⁻¹).
    intros n ϵ.
    specialize (H n (ext ϵ I ∘ (eq_iso (diag_comp n I))⁻¹)).
    destruct H as [f [Hf H]].
    exists f.
    simpl in Hf, H |- *.
    split.
    - intros x.
      do 2 change (from ?i) with (to i⁻¹) in *.
      etransitivity.
      apply (f_equal (fun f => _ ∘ f ∘ _)).
      apply is_eq_unique, is_eq_id.
      apply (transform_is_eq ((eq_iso (diag_comp l I ⁻¹)) ⁻¹)).
      apply is_eq_inv.
      apply eq_iso_is_eq.
      rewrite comp_id_r.
      rewrite <- comp_assoc.
      rewrite Hf.
      simpl.
      change (from ?i) with (to i⁻¹) in *.
      clear.
      rewrite comp_assoc.
      change (to (eq_iso e) x ∘ ext (ext ϵ I) I⁻¹ x ∘ to (eq_iso (diag_comp n I)) ⁻¹ (to I ⁻¹ x) = ϵ x).
      etransitivity.
      apply f_equal.
      apply (is_eq_unique _ ()).
      rewrite H0.
      exists eq_refl.
      set (to (eq_iso (diag_comp l I ⁻¹)) ⁻¹ x).
      simpl in h.
      assert (η (to I⁻¹ x) ∘ to (eq_iso (diag_comp l (I⁻¹))) x = )
      assert (x = (I ∘ I⁻¹) x).
        symmetry.
        now rewrite inv_r.
      rewrite H0.
      simpl.
      change (from ?i) with (to i⁻¹) in *.
      specialize (Hf (to I⁻¹ x)).

      change (to I (to I⁻¹ x)) with ((I ∘ I⁻¹) x) in Hf.
      rewrite (inv_r I) in Hf.
      rewrite <- comp_id_r.
      change (id n) with (id (Δ))
      rewrite <- inv
    unshelve econstructor.

    assert (E: (F ∘ I ∘ I ⁻¹) = F).
      rewrite <- comp_assoc.
      rewrite inv_r.
      apply comp_id_r.
    specialize (H (F ∘ I)).
    destruct H as [L H].
    unshelve eexists.
    unshelve econstructor.
    exact (vertex L).
    intros x.
    eapply comp.
    2: apply (edge L (to I⁻¹ x)).
    change ((F ∘ I ∘ I⁻¹) x ~> F x).
    apply transform.
    change (F ∘ I ∘ I⁻¹ ~> F).
    apply eq_iso, E.
    all: simpl.
    intros x y f.
    etransitivity.
    apply comp_assoc.
    etransitivity.
    apply (f_equal (fun f => f ∘ _)).
    symmetry.
    apply (naturality (to (eq_iso E)) f).
    etransitivity.
    symmetry.
    apply comp_assoc.
    apply f_equal.
    apply (edge_comm L).
    intros N.
    simpl.
    red.
    exact ()

    rewrite <- nat_cone_inv in H.
    revert H.
    generalize (vertex L) (nat_cone L).
    clear L.
    intros l η H.
    unshelve eexists.
    unshelve eapply cone_nat.
    exact l.
    set (ext η I⁻¹).
    eapply comp.
    apply eq_iso, E.
    eapply comp.
    2: apply inv, eq_iso.
    apply eq_iso, (comp_assoc F).
    eapply mov.
    2: exact η.
    2: exact (edge L (I⁻¹ x)).
    change ((F ∘ I ∘ I⁻¹) x ~> F x).
    apply transform.
    change ((F ∘ I ∘ I ⁻¹) ~> F).
    exact (eq_iso E).
    all: simpl.
    intros x y f.
    rewrite comp_assoc.
    etransitivity.
    apply f_equal2.
    symmetry.
    apply (@naturality D).
    rewrite <- naturality.
Qed.*)
