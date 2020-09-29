Require Export Instances Comma.Cone.

Definition is_limit {C D: Category} (F: D ~> C) (L: Cone F) :=
  forall N: Cone F, exists f: N ~> L, forall f', f = f'.

(*Definition is_limit' {C D: Category} (F: D ~> C) (L: Δ ↓ @Δ _ 1 F) :=
  forall N: Δ ↓ @Δ _ 1 F, exists f: N ~> L, forall f', f = f'.

Lemma is_limit_alt {C D: Category} (F: D ~> C) (L: Cone F): is_limit F L <-> is_limit' F (to (CommaCone F)⁻¹ L).
Proof.
  split.
  + intros Hl N'.
    assert (exists N: Cones F, to (CommaCone F)⁻¹ N = N').
    exists (to (CommaCone F) N').
    specialize (inv_l (CommaCone F)) as H.
    apply fun_eq, proj1 in H.
    exact (H N').
    destruct H as [N H].
    subst N'.
    specialize (Hl N).
    destruct Hl as [f Hf].
    exists (fmap (to (CommaCone F)⁻¹) f).
    intros g'.
    assert (exists g: N ~> L, fmap (to (CommaCone F)⁻¹) g = g').
    exists (to (eq_iso (inv_r (CommaCone F))) L ∘ fmap (to (CommaCone F)) g' ∘ to (eq_iso (inv_r (CommaCone F)))⁻¹ N).
    rewrite !fmap_comp.
    transitivity (
      to (eq_iso (inv_l (CommaCone F))) (to (CommaCone F)⁻¹ L) ∘
      fmap ((CommaCone F) ⁻¹ ∘ (CommaCone F)) g' ∘
      to (eq_iso (inv_l (CommaCone F)))⁻¹ (to (CommaCone F)⁻¹ N)
    ).
    f_equal.
    f_equal.
    1, 2: apply is_eq_unique.
    1, 3: apply fmap_is_eq.
    apply (transform_is_eq (to (eq_iso (inv_r (CommaCone F))))), eq_iso_is_eq.
    apply (transform_is_eq (to (eq_iso (inv_r (CommaCone F)))⁻¹)), is_eq_inv, eq_iso_is_eq.
    apply (transform_is_eq (to (eq_iso (inv_l (CommaCone F))))), eq_iso_is_eq.
    apply (transform_is_eq (to (eq_iso (inv_l (CommaCone F)))⁻¹)), is_eq_inv, eq_iso_is_eq.
    generalize (inv_l (CommaCone F)).
    intros e.
    rewrite e; clear e.
    simpl.
    etransitivity.
    apply comp_id_r.
    apply comp_id_l.
    destruct H as [g H].
    subst g'.
    f_equal.
    apply Hf.
  + intros Hl N.
    specialize (Hl (to (CommaCone F)⁻¹ N)).
    destruct Hl as [f' Hf].
    assert (exists f: N ~> L, fmap (to (CommaCone F)⁻¹) f = f').
    exists (to (eq_iso (inv_r (CommaCone F))) L ∘ fmap (to (CommaCone F)) f' ∘ to (eq_iso (inv_r (CommaCone F)))⁻¹ N).
    rewrite !fmap_comp.
    transitivity (
      to (eq_iso (inv_l (CommaCone F))) (to (CommaCone F)⁻¹ L) ∘
      fmap ((CommaCone F) ⁻¹ ∘ (CommaCone F)) f' ∘
      to (eq_iso (inv_l (CommaCone F)))⁻¹ (to (CommaCone F)⁻¹ N)
    ).
    f_equal.
    f_equal.
    1, 2: apply is_eq_unique.
    1, 3: apply fmap_is_eq.
    apply (transform_is_eq (to (eq_iso (inv_r (CommaCone F))))), eq_iso_is_eq.
    apply (transform_is_eq (to (eq_iso (inv_r (CommaCone F)))⁻¹)), is_eq_inv, eq_iso_is_eq.
    apply (transform_is_eq (to (eq_iso (inv_l (CommaCone F))))), eq_iso_is_eq.
    apply (transform_is_eq (to (eq_iso (inv_l (CommaCone F)))⁻¹)), is_eq_inv, eq_iso_is_eq.
    generalize (inv_l (CommaCone F)).
    intros e.
    rewrite e; clear e.
    simpl.
    etransitivity.
    apply comp_id_r.
    apply comp_id_l.
    destruct H as [f H].
    subst f'.
    exists f.
    intros g.
    specialize (Hf (fmap (to (CommaCone F)⁻¹) g)).*)

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

Definition ex_limit {C D: Category} (F: D ~> C) :=
  exists L, is_limit F L.

Lemma ex_limit_alt {C D: Category} (F: D ~> C): ex_limit F <-> exists l (η: Δ l ~> F), forall n (ϵ: Δ n ~> F), exists! f: n ~> l, η ∘ fmap Δ f = ϵ.
Proof.
  split.
  + intros [L H].
    exists (Cone.vertex L).
    exists (nat_cone L).
    intros n η.
    specialize (H (cone_nat n η)).
    destruct H as [f H].
    exists f.
    split.
    natural_eq x.
    apply (Cone.mediator_comm f).
    intros f' H1.
    change (Cone.vertex (cone_nat n η) ~> Cone.vertex L) in f'.
    specialize (proj1 (natural_eq _ _) H1) as H0.
    simpl in H0.
    clear H1.
    specialize (H {| Cone.mediator := f'; Cone.mediator_comm := H0 |}).
    now apply Cone.hom_eq in H.
  + intros [l [η H]].
    exists (cone_nat l η).
    intros N.
    specialize (H (Cone.vertex N) (nat_cone N)).
    destruct H as [f [H1 H]].
    change (Cone.vertex N ~> Cone.vertex (cone_nat l η)) in f.
    specialize (proj1 (natural_eq _ _) H1) as Hf.
    simpl in Hf.
    clear H1.
    exists {| Cone.mediator := f; Cone.mediator_comm := Hf |}.
    intros f'.
    Cone.hom_eq.
    apply H.
    natural_eq x.
    apply (Cone.mediator_comm f').
Qed.

Instance ex_limit_iso {C D: Category}: Proper (isomorphic (Fun C D) ==> iff) ex_limit.
Proof.
  enough (Proper (isomorphic (Fun C D) ==> impl) ex_limit).
  now split; apply H.
  intros F G [I].
  rewrite !ex_limit_alt.
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
  forall F: D ~> C, ex_limit F.

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
(*
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
*)
Definition is_lim {D C: Category} (F: Fun D C ~> C) := Δ -| F.
Definition ex_lim (D C: Category) := exists F: Fun D C ~> C, is_lim F.

Definition is_colim {D C: Category} (F: Fun D C ~> C) := F -| Δ.
Definition ex_colim (D C: Category) := exists F: Fun D C ~> C, is_colim F.

Lemma ex_lim_correct (D C: Category): ex_lim D C -> has_limit D C.
Proof.
  intros [L [ɛ [η adj]]] F.
  apply adjoint_by_alt in adj.
  destruct adj as [adj1 adj2].
  apply ex_limit_alt.
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

(*Lemma ex_colim_correct (D C: Category): ex_colim D C -> has_colimit D C.
Proof.
  intros [L [ɛ [η adj]]] F.
  apply adjoint_by_alt in adj.
  destruct adj as [adj1 adj2].
  apply ex_limit_alt.
  exists (L F).
  unshelve eexists.
  unshelve eexists.
  exact (transform (η F)).
  intros x y f.
  symmetry.
  exact (naturality (η F) f).
  intros n ϵ.
  exists (ɛ n ∘ fmap L ϵ).
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
Qed.*)

Definition Colim {D C: Category}: co (Fun (Fun D C) C) <~> Fun (Fun (co D) (co C)) (co C) := Comp_r_iso (CoFun D C)⁻¹ · CoFun (Fun D C) C.

Lemma is_lim_co {D C: Category} (F: Fun D C ~> C): is_lim (to Colim F) <-> is_colim F.
Proof.
  change (Δ -| to (CoFun (Fun D C) C) F ∘ (CoFun D C)⁻¹ <-> F -| Δ).
  replace (@Δ (co C) (co D)) with (to (CoFun D C) ∘ to (CoFun C (Fun D C)) (@Δ C D)).
  rewrite (adjoint_co F Δ).
  apply (adjoint_comp_iso_r _ _ ((CoFun D C) ⁻¹)).
  clear.
  fun_eq x y f.
  unfold cof.
  simpl.
  fun_eq a b f.
  now rewrite !eq_iso_refl.
  natural_eq a.
  rewrite (is_eq_refl (to (eq_iso H) a)).
  rewrite (is_eq_refl (to (eq_iso H0) a)).
  simpl.
  rewrite comp_id_r.
  apply comp_id_l.
  1: apply (transform_is_eq (eq_iso H0)).
  2: apply (transform_is_eq (eq_iso H)).
  all: apply eq_iso_is_eq.
Qed.

Lemma ex_lim_co {D C: Category}: ex_lim (co D) (co C) <-> ex_colim D C.
Proof.
  split.
  + intros [F' H].
    assert (exists F: Fun D C ~> C, to Colim F = F').
    exists (to Colim⁻¹ F').
    change ((Colim ∘ Colim⁻¹) F' = F').
    now rewrite inv_r.
    destruct H0 as [F HF].
    subst F'.
    exists F.
    apply is_lim_co, H.
  + intros [F H].
    exists (to Colim F).
    apply is_lim_co, H.
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
    apply ex_limit_alt in H.
    apply ex_limit_alt.
    destruct H as [l [η H]].
    assert (exists η': Δ l ∘ I ~> F ∘ I, η' ∘ (eq_iso (diag_comp l I))⁻¹ = η).
      exists (η ∘ (eq_iso (diag_comp l I))).
      rewrite <- comp_assoc.
      rewrite inv_r.
      apply comp_id_r.
    destruct H0 as [η' Hη].
    subst η.
    assert (exists η: Δ l ~> F, η |> I = η').
      exists (ρ F ∘ (F <| eq_iso (inv_r I)) ∘ (α F I I⁻¹)⁻¹ ∘ (η' |> I⁻¹) ∘ (α (Δ l) I I⁻¹) ∘ (Δ l <| (eq_iso (inv_r I))⁻¹) ∘ (ρ (Δ l))⁻¹).
      natural_eq x.
      rewrite !comp_id_l, !comp_id_r.
      etransitivity.
      apply (f_equal (fun f => fmap F f ∘ _)).
      apply (is_eq_unique (to (eq_iso (inv_r I)) (to I x)) (fmap (to I) (to (eq_iso (inv_l I)) x))).
      apply transform_is_eq, eq_iso_is_eq.
      apply (fmap_is_eq I), (transform_is_eq (to (eq_iso (inv_l I)))), eq_iso_is_eq.
      change ((((F ∘ I) <| eq_iso (inv_l I)) ∘ (η' |> (I⁻¹ ∘ I))) x = η' x).
      rewrite eq_iso_whisk_l.
      apply comp_id_r.
      apply eq_iso_is_eq.
    destruct H0 as [η Hη].
    subst η'.
    exists l, η.
    intros n ϵ.
    specialize (H n ((ϵ |> I) ∘ (eq_iso (diag_comp n I))⁻¹)).
    destruct H as [f Hf].
    exists f; split; [apply proj1 in Hf | apply proj2 in Hf].
    generalize (proj1 (natural_eq _ _ ) Hf).
    clear Hf; intros Hf.
    natural_eq x.
    specialize (Hf (to I⁻¹ x)).
    simpl in Hf.
    set (e1 := to (eq_iso (diag_comp n I))⁻¹ (to I⁻¹ x)).
    set (e2 := to (eq_iso (diag_comp l I))⁻¹ (to I⁻¹ x)).
    change (η (to I (to I⁻¹ x)) ∘ e2 ∘ f = ϵ (to I (to I⁻¹ x)) ∘ e1) in Hf.
    rewrite (is_eq_refl e1) in Hf.
    rewrite (is_eq_refl e2) in Hf.
    clear e1 e2.
    rewrite !comp_id_r in Hf.
    specialize (inv_r I) as H.
    apply fun_eq, proj1 in H.
    specialize (H x).
    change (to I (to I⁻¹ x) = x) in H.
    rewrite H in Hf.
    exact Hf.
    1, 2: unfold e1, e2; clear.
    1: apply (transform_is_eq (to (eq_iso (diag_comp l I))⁻¹)).
    2: apply (transform_is_eq (to (eq_iso (diag_comp n I))⁻¹)).
    1, 2: apply is_eq_inv, eq_iso_is_eq.
    intros g Hg.
    specialize (Hf g).
    apply Hf.
    natural_eq x.
    change (from ?i) with (to i⁻¹).
    etransitivity.
    2: etransitivity.
    apply (f_equal (fun f => _ ∘ f ∘ _)).
    3: apply f_equal.
    3: symmetry.
    1, 3: apply is_eq_refl.
    1: apply (transform_is_eq (to (eq_iso (diag_comp l I))⁻¹)).
    2: apply (transform_is_eq (to (eq_iso (diag_comp n I))⁻¹)).
    1, 2: apply is_eq_inv, eq_iso_is_eq.
    rewrite !comp_id_r.
    apply (proj1 (natural_eq _ _ ) Hg).
  + intros H F.
    specialize (H (I⁻¹ ∘ F)).
    apply ex_limit_alt in H.
    apply ex_limit_alt.
    destruct H as [l [η H]].
    assert (exists l': T, to I⁻¹ l' = l).
      exists (to I l).
      specialize (inv_l I) as Hi.
      apply fun_eq, proj1 in Hi.
      apply Hi.
    destruct H0 as [l' Hl].
    subst l.
    rename l' into l.
    assert (exists η': I⁻¹ ∘ Δ l ~> I⁻¹ ∘ F, η' ∘ (eq_iso (comp_diag I⁻¹ l))⁻¹ = η).
      exists (η ∘ eq_iso (comp_diag I⁻¹ l)).
      rewrite <- comp_assoc.
      rewrite inv_r.
      apply comp_id_r.
    destruct H0 as [η' Hη].
    subst η.
    assert (exists η: Δ l ~> F, I⁻¹ <| η = η').
      exists (λ F ∘ (eq_iso (inv_r I) |> F) ∘ (α I I⁻¹ F) ∘ (I <| η') ∘ (α I I⁻¹ (Δ l))⁻¹ ∘ ((eq_iso (inv_r I))⁻¹ |> Δ l) ∘ (λ (Δ l))⁻¹).
      natural_eq x.
      rewrite !comp_id_l, !comp_id_r.
      rewrite !fmap_comp.
      etransitivity.
      2: etransitivity.
      apply (f_equal (fun f => f ∘ _ ∘ _)).
      2: apply f_equal.
      1: apply (is_eq_unique _ (to (eq_iso (inv_l I)) (to I⁻¹ (F x)))).
      3: apply (is_eq_unique _ (to (eq_iso (inv_l I))⁻¹ (to I⁻¹ l))).
      1, 3: apply (fmap_is_eq (I⁻¹)).
      1: apply (transform_is_eq (to (eq_iso (inv_r I)))).
      2: apply (transform_is_eq (to (eq_iso (inv_r I))⁻¹)).
      3, 4: apply transform_is_eq.
      2, 4: apply is_eq_inv.
      1, 2, 3, 4: apply eq_iso_is_eq.
      change (((eq_iso (inv_l I) |> (I⁻¹ ∘ F)) ∘ ((I⁻¹ ∘ I) <| η') ∘ ((eq_iso (inv_l I))⁻¹ |> (I⁻¹ ∘ Δ l))) x = η' x).
      rewrite eq_iso_whisk_r.
      rewrite <- comp_assoc.
      rewrite <- whisk_comp_distr_r.
      rewrite inv_r.
      simpl.
      apply comp_id_r.
      apply eq_iso_is_eq.
    destruct H0 as [η Hη].
    subst η'.
    exists l, η.
    intros n ϵ.
    specialize (H (to I⁻¹ n) ((I⁻¹ <| ϵ) ∘ (eq_iso (comp_diag I⁻¹ n))⁻¹)).
    destruct H as [f' Hf].
    assert (exists f: n ~> l, fmap (to I⁻¹) f = f').
      exists (to (eq_iso (inv_r I)) l ∘ fmap (to I) f' ∘ to (eq_iso (inv_r I))⁻¹ n).
      rewrite !fmap_comp.
      etransitivity.
      etransitivity.
      apply (f_equal (fun f => f ∘ _ ∘ _)).
      2: apply f_equal.
      1: apply (is_eq_unique _ (to (eq_iso (inv_l I)) (to I⁻¹ l))).
      3: apply (is_eq_unique _ (to (eq_iso (inv_l I))⁻¹ (to I⁻¹ n))).
      1, 3: apply (fmap_is_eq (to I⁻¹)).
      1: apply (transform_is_eq (to (eq_iso (inv_r I)))).
      2: apply (transform_is_eq (to (eq_iso (inv_r I))⁻¹)).
      3, 4: apply transform_is_eq.
      2, 4: apply is_eq_inv.
      1, 2, 3, 4: apply eq_iso_is_eq.
      etransitivity.
      apply (f_equal (fun f => f ∘ _)).
      apply (naturality (to (eq_iso (inv_l I)))).
      rewrite <- comp_id_r.
      rewrite <- comp_assoc.
      f_equal.
      change ((eq_iso (inv_l I) ∘ (eq_iso (inv_l I))⁻¹) (to I⁻¹ n) = id (to I⁻¹ n)).
      now rewrite inv_r.
    destruct H as [f H].
    subst f'.
    exists f; split; [apply proj1 in Hf | apply proj2 in Hf].
    generalize (proj1 (natural_eq _ _) Hf).
    clear Hf; intros Hf.
    simpl in Hf.
    repeat change (from ?i) with (to i⁻¹) in Hf.
    natural_eq x.
    specialize (Hf x).
    set (e1 := to (eq_iso (comp_diag (I⁻¹) n))⁻¹ x).
    set (e2 := to (eq_iso (comp_diag (I⁻¹) l))⁻¹ x).
    change (fmap (to I⁻¹) (η x) ∘ e2 ∘ fmap (to I⁻¹) f = fmap (to I⁻¹) (ϵ x) ∘ e1) in Hf.
    rewrite (is_eq_refl e1) in Hf.
    rewrite (is_eq_refl e2) in Hf.
    rewrite !comp_id_r in Hf.
    setoid_rewrite <- (fmap_comp (η x)) in Hf.
    apply fmap_monic_inj in Hf.
    exact Hf.
    apply iso_monic.
    1, 2: unfold e1, e2; clear.
    1: apply (transform_is_eq (eq_iso (comp_diag I⁻¹ l))⁻¹).
    2: apply (transform_is_eq (eq_iso (comp_diag I⁻¹ n))⁻¹).
    1, 2: apply is_eq_inv, eq_iso_is_eq.
    intros g Hg.
    specialize (Hf (fmap (to I⁻¹) g)).
    eapply fmap_monic_inj, Hf.
    apply iso_monic.
    clear Hf.
    generalize (proj1 (natural_eq _ _) Hg).
    clear Hg; intros Hg.
    natural_eq x.
    specialize (Hg x).
    simpl in Hg.
    change (from ?i) with (to i⁻¹).
    etransitivity.
    etransitivity.
    apply (f_equal (fun f => _ ∘ f ∘ _)).
    3: apply f_equal.
    3: symmetry.
    1, 3: apply is_eq_refl.
    1: apply (transform_is_eq (eq_iso (comp_diag (from I) l))⁻¹).
    2: apply (transform_is_eq (eq_iso (comp_diag (from I) n))⁻¹).
    1, 2: apply is_eq_inv, eq_iso_is_eq.
    rewrite !comp_id_r.
    rewrite <- fmap_comp.
    f_equal.
    exact Hg.
Qed.

Instance ex_lim_iso: Proper (isomorphic Cat ==> isomorphic Cat ==> iff) ex_lim.
Proof.
  enough (Proper (isomorphic Cat ==> isomorphic Cat ==> impl) ex_lim).
  now split; apply H.
  intros C D I S T J.
  transitivity (ex_lim D S).
  1: clear J T; destruct I as [I].
  2: clear I C; destruct J as [I].
  all: intros [F H].
  all: red in H.
  + exists (F ∘ (Comp_r I)).
    red.
    replace (@Δ S D) with (Comp_r I⁻¹ ∘ @Δ S C).
    apply adjoint_comp.
    exact H.
    apply (iso_adjoint (Comp_r_iso I⁻¹)).
    clear.
    fun_eq x y f.
    apply diag_comp.
    change (Δ x ∘ I⁻¹ = Δ x) in H.
    change (Δ y ∘ I⁻¹ = Δ y) in H0.
    natural_eq a.
    etransitivity.
    etransitivity.
    apply (f_equal (fun f => f ∘ _)).
    3: apply f_equal.
    3: symmetry.
    1, 3: apply is_eq_refl.
    1: apply (transform_is_eq (eq_iso H0)).
    2: apply (transform_is_eq (eq_iso H)).
    1, 2: apply eq_iso_is_eq.
    rewrite comp_id_r.
    apply comp_id_l.
  + exists (I ∘ F ∘ (Comp_l I⁻¹)).
    red.
    rewrite <- (comp_id_l Δ).
    rewrite <- (inv_r (Comp_l_iso I)).
    rewrite <- comp_assoc.
    apply adjoint_comp, iso_adjoint.
    rewrite <- (comp_id_r (_ ∘ _)).
    rewrite <- (inv_r I).
    rewrite comp_assoc.
    apply adjoint_comp.
    apply iso_adjoint.
    simpl.
    unfold Comp_l_iso, from; simpl.
    change (from I) with (to I⁻¹).
    replace (Comp_l I⁻¹ ∘ @Δ T D ∘ I) with (@Δ S D).
    exact H.
    clear.
    fun_eq x y f.
    change (@Δ S D x = I⁻¹ ∘ Δ (to I x)).
    symmetry.
    rewrite <- comp_diag.
    rewrite comp_assoc.
    rewrite inv_l.
    exact (comp_id_l (Δ x)).
    change (@Δ S D x = I⁻¹ ∘ Δ (to I x)) in H.
    change (@Δ S D y = I⁻¹ ∘ Δ (to I y)) in H0.
    natural_eq a.
    change (fmap (from I) _) with (fmap (I⁻¹ ∘ I) f).
    etransitivity.
    etransitivity.
    apply (f_equal (fun f => f ∘ _)).
    3: apply f_equal.
    apply (is_eq_unique _ (to (eq_iso (inv_l I))⁻¹ y)).
    4: apply (is_eq_unique (to (eq_iso (inv_l I))⁻¹ x) _).
    3: apply (naturality (to (eq_iso (inv_l I))⁻¹)).
    1: apply (transform_is_eq (eq_iso H0)).
    4: apply (transform_is_eq (eq_iso H)).
    2, 3: apply transform_is_eq, is_eq_inv.
    all: apply eq_iso_is_eq.
Qed.
