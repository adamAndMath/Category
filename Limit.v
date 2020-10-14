Require Export Instances Comma.Cone.
Require Export Finite.

Definition is_limit {D C: Category} (F: D ~> C) (L: Cone F) :=
  forall N: Cone F, exists f: N ~> L, forall f', f = f'.

Instance is_limit_iso {D C: Category} (F: D ~> C): Proper (isomorphic _ ==> iff) (is_limit F).
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

Definition is_limit' {D C: Category} (F: D ~> C) (l: C) (η: Δ l ~> F) :=
  forall n (ϵ: Δ n ~> F), exists! f: n ~> l, η ∘ fmap Δ f = ϵ.

Lemma is_limit_alt {D C: Category} (F: D ~> C) (L: Cone F): is_limit F L <-> is_limit' F (Cone.vertex L) (nat_cone L).
Proof.
  split.
  + intros H n ϵ.
    specialize (H (cone_nat n ϵ)).
    destruct H as [u Hu].
    exists u.
    split.
    natural_eq x.
    apply (Cone.mediator_comm u).
    intros u' H.
    generalize (fun u' H => proj1 (Cone.hom_eq _ _ _) (Hu {| Cone.mediator := u'; Cone.mediator_comm := H |})).
    clear Hu; intros Hu.
    simpl in Hu.
    apply Hu; clear Hu.
    exact (proj1 (natural_eq (nat_cone L ∘ fmap Δ u') ϵ) H).
  + intros H N.
    specialize (H (Cone.vertex N) (nat_cone N)).
    destruct H as [u Hu].
    unshelve eexists.
    exists u.
    2: intros u'.
    2: Cone.hom_eq.
    exact (proj1 (natural_eq (nat_cone L ∘ fmap Δ u) (nat_cone N)) (proj1 Hu)).
    apply Hu.
    natural_eq x.
    apply Cone.mediator_comm.
Qed.

Lemma is_limit_alt' {D C: Category} (F: D ~> C) (l: C) (η: Δ l ~> F): is_limit' F l η <-> is_limit F (cone_nat l η).
Proof.
  split.
  + intros H N.
    specialize (H (Cone.vertex N) (nat_cone N)).
    destruct H as [u Hu].
    unshelve eexists.
    exists u.
    2: intros u'.
    2: Cone.hom_eq.
    simpl.
    exact (proj1 (natural_eq (η ∘ fmap Δ u) (nat_cone N)) (proj1 Hu)).
    apply Hu.
    natural_eq x.
    apply (Cone.mediator_comm u').
  + intros H n ϵ.
    specialize (H (cone_nat n ϵ)).
    destruct H as [u Hu].
    exists u.
    split.
    natural_eq x.
    apply (Cone.mediator_comm u).
    intros u' H.
    generalize (fun u' H => proj1 (Cone.hom_eq _ _ _) (Hu {| Cone.mediator := u'; Cone.mediator_comm := H |})).
    clear Hu; intros Hu.
    simpl in Hu.
    apply Hu; clear Hu.
    exact (proj1 (natural_eq (η ∘ fmap Δ u') ϵ) H).
Qed.

Definition is_limit_obj {D C: Category} (F: D ~> C) (l: C) :=
  exists L, Cone.vertex L = l /\ is_limit F L.

Definition ex_limit {D C: Category} (F: D ~> C) :=
  exists L, is_limit F L.

Lemma limit_obj_ex {D C: Category} (F: D ~> C) (l: C): is_limit_obj F l -> ex_limit F.
Proof.
  intros [L [_ H]].
  now exists L.
Qed.

Lemma is_limit_obj_alt {D C: Category} (F: D ~> C) (l: C): is_limit_obj F l <-> exists η: Δ l ~> F, is_limit' F l η.
Proof.
  split.
  + intros [L [Hl H]].
    subst l.
    exists (nat_cone L).
    apply is_limit_alt, H.
  + intros [η H].
    exists (cone_nat l η).
    split.
    reflexivity.
    apply is_limit_alt', H.
Qed.

Lemma ex_limit_alt {D C: Category} (F: D ~> C): ex_limit F <-> exists l (η: Δ l ~> F), is_limit' F l η.
Proof.
  split.
  + intros [L H].
    exists (Cone.vertex L), (nat_cone L).
    apply is_limit_alt, H.
  + intros [l [η H]].
    exists (cone_nat l η).
    apply is_limit_alt', H.
Qed.

Instance ex_limit_iso {D C: Category}: Proper (isomorphic (Fun D C) ==> iff) ex_limit.
Proof.
  enough (Proper (isomorphic (Fun D C) ==> impl) ex_limit).
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

Instance limit_obj_iso {D C: Category}: Proper (isomorphic (Fun D C) ==> isomorphic C ==> iff) is_limit_obj.
Proof.
  enough (Proper (isomorphic (Fun D C) ==> isomorphic C ==> impl) is_limit_obj).
  now split; apply H.
  intros F G H l1 l2 H0.
  transitivity (is_limit_obj F l2).
  1: clear G H; rename H0 into H.
  2: clear l1 H0; rename l2 into l.
  + intros [L [Hl HL]].
    subst l1.
    destruct (cone_iso_ex L l2 H) as [L2 [Hl H0]].
    clear H; rename H0 into H.
    exists L2.
    split.
    assumption.
    now rewrite <- H.
  + intros [L [Hl HL]].
    destruct H as [I].
    subst l.
    exists (cone_lift F G (to I) L).
    split.
    reflexivity.
    intros N'.
    assert (exists N, cone_lift F G I N = N').
    exists (cone_lift G F (to I⁻¹) N').
    apply Cone.obj_eq; simpl; split.
    reflexivity.
    intros x e.
    rewrite eq_iso_refl; clear e.
    simpl.
    rewrite comp_id_r.
    rewrite comp_assoc.
    change (to I x ∘ from I x) with ((I ∘ I⁻¹) x).
    rewrite inv_r.
    apply comp_id_l.
    destruct H as [N].
    subst N'.
    specialize (HL N).
    destruct HL as [f Hf].
    exists (fmap (cone_lift F G I) f).
    intros g'.
    assert (exists g, fmap (cone_lift F G I) g = g').
    destruct g' as [g Hg].
    simpl in g, Hg.
    unshelve eexists.
    exists g.
    2: Cone.hom_eq.
    intros x.
    apply (is_iso_monic (to I x)).
    apply is_iso_transform, iso_is_iso.
    rewrite comp_assoc.
    apply Hg.
    reflexivity.
    destruct H as [g].
    subst g'.
    f_equal.
    apply Hf.
Qed.

Lemma iso_limit {D C: Category} (F: D ~> C) (L1 L2: Cone F): is_limit F L1 -> is_limit F L2 -> L1 ≃ L2.
Proof.
  intros H1 H2.
  destruct (H2 L1) as [f _].
  destruct (H1 L2) as [g _].
  specialize (H1 L1).
  destruct H1 as [i1 H1].
  specialize (H2 L2).
  destruct H2 as [i2 H2].
  constructor.
  exists f, g.
  1: transitivity i1.
  3: transitivity i2.
  all: easy.
Qed.

Definition has_limit (D C: Category) :=
  forall F: D ~> C, ex_limit F.

Definition is_colimit {D C: Category} (F: D ~> C) := is_limit (cof F).

Instance is_colimit_iso {D C: Category} (F: D ~> C): Proper (isomorphic _ ==> iff) (is_limit F).
Proof. apply is_limit_iso. Qed.

Definition is_colimit' {D C: Category} (F: D ~> C) (l: C) (η: F ~> Δ l) :=
  forall (n: C) (ϵ: F ~> Δ n), exists! f: l ~> n, fmap Δ f ∘ η = ϵ.

Definition is_colimit_obj {D C: Category} (F: D ~> C) (l: C) :=
  exists L, Cone.vertex L = (l: co C) /\ is_colimit F L.

Instance colimit_obj_iso {D C: Category}: Proper (isomorphic (Fun D C) ==> isomorphic C ==> iff) is_limit_obj.
Proof. apply limit_obj_iso. Qed.

Definition ex_colimit {D C: Category} (F: D ~> C) :=
  exists L, is_colimit F L.

Instance ex_colimit_iso {D C: Category}: Proper (isomorphic (Fun D C) ==> iff) ex_limit.
Proof. apply ex_limit_iso. Qed.

Definition has_colimit (D C: Category) :=
  forall F: D ~> C, ex_colimit F.

Lemma is_limit_co {D C: Category} (F: D ~> C) (L: Cone (cof F)): is_limit (cof F) L <-> is_colimit F L.
Proof. reflexivity. Qed.

Lemma limit_obj_co {D C: Category} (F: D ~> C) (l: C): is_limit_obj (cof F) l <-> is_colimit_obj F l.
Proof. reflexivity. Qed.

Lemma ex_limit_co {D C: Category} (F: D ~> C): ex_limit (cof F) <-> ex_colimit F.
Proof. reflexivity. Qed.

Lemma has_limit_co (D C: Category): has_limit (co D) (co C) <-> has_colimit D C.
Proof.
  split.
  all: intros H F.
  apply H.
  assert (exists F', cof F' = F).
  exists (cof' F).
  apply cof_inv_r.
  destruct H0 as [F'].
  subst F.
  apply ex_limit_co, H.
Qed.

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

Lemma ex_colim_correct (D C: Category): ex_colim D C -> has_colimit D C.
Proof.
  rewrite <- ex_lim_co, <- has_limit_co.
  apply ex_lim_correct.
Qed.

Instance has_limit_iso2: Proper (cequiv ==> cequiv ==> iff) has_limit.
Proof.
  enough (Proper (cequiv ==> cequiv ==> impl) has_limit).
  now split; apply H.
  intros A B H1 C D H2.
  rewrite cequiv_ex in H1, H2.
  transitivity (has_limit B C).
  1: clear D H2; destruct H1 as [I].
  2: clear A H1; destruct H2 as [I].
  + intros H F.
    specialize (H (F ∘ I)).
    apply ex_limit_alt in H.
    apply ex_limit_alt.
    destruct H as [l [ι H]].
    assert (exists ι': Δ l ∘ I ~> F ∘ I, ι' ∘ (eq_iso (diag_comp l I))⁻¹ = ι).
      exists (ι ∘ (eq_iso (diag_comp l I))).
      rewrite <- comp_assoc, inv_r.
      apply comp_id_r.
    destruct H0 as [ι'].
    subst ι.
    assert (exists ι: Δ l ~> F, ι |> I = ι').
      exists (ρ F ∘ (F <| iunit I⁻) ∘ (α F I I⁻)⁻¹ ∘ (ι' |> I⁻) ∘ α (Δ l) I I⁻ ∘ (Δ l <| (iunit I⁻)⁻¹) ∘ (ρ (Δ l))⁻¹).
      natural_eq x.
      rewrite comp_id_l, !comp_id_r.
      rewrite <- iunit_to.
      change (fmap (F ∘ I) (to (iunit I) x) ∘ ι' (I⁻ (I x)) = ι' x).
      rewrite <- naturality.
      apply comp_id_r.
    destruct H0 as [ι].
    subst ι'.
    exists l, ι.
    intros n δ.
    specialize (H n (δ |> I ∘ (eq_iso (diag_comp n I))⁻¹)).
    destruct H as [f Hf].
    exists f.
    split; [apply proj1 in Hf | apply proj2 in Hf].
    generalize (proj1 (natural_eq _ _) Hf).
    clear Hf; intros Hf.
    simpl in Hf.
    natural_eq y.
    specialize (Hf (I⁻ y)).
    setoid_rewrite (is_eq_refl (from (eq_iso (diag_comp l I)) (I ⁻ y))) in Hf.
    setoid_rewrite (is_eq_refl (from (eq_iso (diag_comp n I)) (I ⁻ y))) in Hf.
    simpl in Hf.
    rewrite !comp_id_r in Hf.
    setoid_rewrite <- (comp_id_r (ι y)).
    setoid_rewrite <- (comp_id_r (δ y)).
    simpl.
    change (id l) with (fmap (Δ l) (to (iunit I⁻) y)).
    change (id n) with (fmap (Δ n) (to (iunit I⁻) y)).
    setoid_rewrite (@naturality _ _ _ _ ι).
    setoid_rewrite (@naturality _ _ _ _ δ).
    rewrite <- comp_assoc.
    now f_equal.
    1: apply (transform_is_eq (eq_iso (diag_comp n I))⁻¹).
    2: apply (transform_is_eq (eq_iso (diag_comp l I))⁻¹).
    1, 2: apply is_eq_inv, eq_iso_is_eq.
    intros g Hg.
    apply Hf; clear Hf.
    generalize (proj1 (natural_eq _ _) Hg).
    clear Hg; intros Hg.
    natural_eq y.
    setoid_rewrite (is_eq_refl (from (eq_iso (diag_comp l I)) y)).
    setoid_rewrite (is_eq_refl (from (eq_iso (diag_comp n I)) y)).
    rewrite !comp_id_r.
    apply Hg.
    1: apply (transform_is_eq (eq_iso (diag_comp n I))⁻¹).
    2: apply (transform_is_eq (eq_iso (diag_comp l I))⁻¹).
    all: apply is_eq_inv, eq_iso_is_eq.
  + intros H F'.
    assert (exists F, I ∘ F ≃ F').
      exists (I⁻ ∘ F').
      rewrite comp_assoc.
      rewrite (inv2_r I).
      rewrite comp_id_l.
      reflexivity.
    destruct H0 as [F].
    rewrite <- H0; clear H0.
    specialize (H F).
    apply ex_limit_alt in H.
    apply ex_limit_alt.
    destruct H as [l [ι H]].
    exists (I l).
    exists (I <| ι ∘ (eq_iso (comp_diag I l))⁻¹).
    intros n δ.
    assert (exists δ', δ' ∘ fmap Δ (to (icounit I)⁻¹ n) = δ).
      exists (δ ∘ fmap Δ (to (icounit I) n)).
      rewrite <- comp_assoc, <- fmap_comp.
      change (to (icounit I) n ∘ _) with ((icounit I ∘ (icounit I)⁻¹) n).
      rewrite inv_r.
      simpl transform.
      rewrite fmap_id.
      apply comp_id_r.
    destruct H0 as [δ'].
    subst δ.
    assert (exists δ, δ ∘ (eq_iso (comp_diag I (I⁻ n))) ⁻¹ = δ').
      exists (δ' ∘ eq_iso (comp_diag I (I⁻ n))).
      rewrite <- comp_assoc, inv_r.
      apply comp_id_r.
    destruct H0 as [δ''].
    subst δ'.
    assert (exists δ, I <| δ = δ'').
      exists (λ F ∘ (iunit I |> F) ∘ α I⁻ I F ∘ (I⁻ <| δ'') ∘ (α I⁻ I (Δ (I⁻ n)))⁻¹ ∘ ((iunit I)⁻¹ |> Δ (I⁻ n)) ∘ (λ (Δ (I⁻ n)))⁻¹).
      natural_eq x.
      rewrite !comp_id_l, !comp_id_r.
      rewrite !fmap_comp.
      setoid_rewrite (iunit_to I (F x)).
      setoid_rewrite (@naturality _ _ _ _ (to (icounit I))).
      rewrite <- iunit_to.
      rewrite <- comp_assoc, <- comp_id_r.
      apply f_equal.
      etransitivity.
      symmetry.
      apply (@fmap_comp _ _ I).
      rewrite <- fmap_id.
      f_equal.
      change ((iunit I ∘ (iunit I)⁻¹) (I⁻ n) = id (id C) (I⁻ n)).
      f_equal.
      apply inv_r.
    destruct H0 as [δ].
    subst δ''.
    specialize (H (I⁻ n) δ).
    destruct H as [f Hf].
    exists (fmap I f ∘ to (icounit I)⁻¹ n).
    split; [apply proj1 in Hf | apply proj2 in Hf].
    rewrite fmap_comp, comp_assoc.
    f_equal.
    generalize (proj1 (natural_eq _ _) Hf).
    clear Hf; intros Hf.
    simpl in Hf.
    natural_eq y.
    setoid_rewrite (is_eq_refl (from (eq_iso (comp_diag I l)) y)).
    setoid_rewrite (is_eq_refl (from (eq_iso (comp_diag I (I⁻ n))) y)).
    rewrite !comp_id_r.
    setoid_rewrite <- (@fmap_comp _ _ I).
    f_equal.
    apply Hf.
    1: apply (transform_is_eq (eq_iso (comp_diag I (I⁻ n)))⁻¹).
    2: apply (transform_is_eq (eq_iso (comp_diag I l))⁻¹).
    1, 2: apply is_eq_inv, eq_iso_is_eq.
    intros g Hg.
    apply (iso2_faithful I⁻).
    rewrite fmap_comp.
    apply (is_iso_monic (to (iunit I) l)).
    apply is_iso_transform, iso_is_iso.
    rewrite comp_assoc.
    etransitivity.
    apply (f_equal (fun f => f ∘ _)).
    apply (@naturality _ _ _ _ (to (iunit I))).
    setoid_rewrite <- (iunit_co' I n).
    rewrite <- comp_assoc.
    etransitivity.
    apply f_equal.
    symmetry.
    apply (@fmap_comp _ _ I⁻).
    change (to (iunit I⁻) n ∘ _) with ((iunit I⁻ ∘ (iunit I⁻)⁻¹) n).
    rewrite inv_r.
    simpl.
    rewrite fmap_id, comp_id_r.
    change (from2 I) with (to2 I⁻).
    apply Hf; clear f Hf.
    generalize (proj1 (natural_eq _ _) Hg).
    clear Hg; intros Hg.
    simpl in Hg.
    natural_eq y.
    specialize (Hg y).
    setoid_rewrite (is_eq_refl (from (eq_iso (comp_diag I l)) y)) in Hg.
    setoid_rewrite (is_eq_refl (from (eq_iso (comp_diag I (I⁻ n))) y)) in Hg.
    setoid_rewrite comp_id_r in Hg.
    destruct (iso2_full I _ _ (g ∘ to (icounit I) n)) as [f H].
    apply (f_equal (fun f => f ∘ to (icounit I)⁻¹ n)) in H.
    rewrite <- comp_assoc in H.
    change (to (icounit I) n ∘ to (icounit I)⁻¹ n) with (((icounit I) ∘ (icounit I)⁻¹) n) in H.
    rewrite inv_r in H.
    simpl transform in H at 2.
    rewrite comp_id_r in H.
    subst g.
    rewrite comp_assoc in Hg.
    apply is_iso_epic in Hg.
    setoid_rewrite <- (@fmap_comp _ _ I) in Hg.
    apply iso2_faithful in Hg.
    rewrite <- Hg.
    f_equal.
    clear ι δ Hg.
    rewrite fmap_comp, comp_assoc.
    etransitivity.
    apply (f_equal (fun f => f ∘ _)).
    apply (@naturality _ _ _ _ (to (iunit I))).
    rewrite <- comp_assoc, <- comp_id_r.
    f_equal.
    rewrite <- iunit_from, <- fmap_id.
    etransitivity.
    symmetry.
    apply (@fmap_comp _ _ I⁻).
    f_equal.
    change ((icounit I ∘ (icounit I)⁻¹) n = id (id D) n).
    f_equal.
    apply inv_r.
    apply (is_iso_transform (icounit I)⁻¹), iso_is_iso.
    1: apply (transform_is_eq (eq_iso (comp_diag I (I⁻ n)))⁻¹).
    2: apply (transform_is_eq (eq_iso (comp_diag I l))⁻¹).
    all: apply is_eq_inv, eq_iso_is_eq.
Qed.

Instance has_limit_iso: Proper (isomorphic Cat ==> isomorphic Cat ==> iff) has_limit | 10.
Proof.
  intros C D I S T J.
  f_equiv.
  all: now apply iso_cequiv.
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

Section preservation.
Context {S T: Category} (F: S ~> T) (D: Category).

Definition preserve :=
  forall (G: D ~> S) L, is_limit G L -> is_limit (F ∘ G) (cone_whisk_l F G L).

Lemma preserve_alt: preserve <-> forall (G: D ~> S) (l: S) (η: Δ l ~> G), is_limit' G l η -> is_limit' (F ∘ G) (F l) ((F <| η) ∘ (eq_iso (comp_diag F l))⁻¹).
Proof.
  split.
  + intros HF G l η HL.
    apply is_limit_alt' in HL.
    apply is_limit_alt'.
    apply HF in HL.
    revert HL.
    change (?P -> ?Q) with (impl P Q).
    f_equiv.
    apply Cone.obj_eq; simpl.
    repeat split.
    intros x e.
    rewrite eq_iso_refl; clear e.
    simpl.
    rewrite comp_id_r.
    rewrite <- (comp_id_r (fmap _ _)) at 1.
    f_equal.
    symmetry.
    apply is_eq_refl.
    apply (transform_is_eq (eq_iso (comp_diag F l))⁻¹).
    apply is_eq_inv, eq_iso_is_eq.
  + intros HF G L HL.
    apply is_limit_alt in HL.
    apply is_limit_alt.
    apply HF in HL.
    revert HL.
    change (?P -> ?Q) with (impl P Q).
    f_equiv.
    natural_eq x.
    rewrite <- comp_id_r.
    f_equal.
    apply is_eq_refl.
    apply (transform_is_eq (eq_iso (comp_diag F (Cone.vertex L)))⁻¹).
    apply is_eq_inv, eq_iso_is_eq.
Qed.

Definition create :=
  forall (G: D ~> S) L, is_limit (F ∘ G) L -> exists L', unique (fun L' => cone_whisk_l F G L' = L) L' /\ is_limit G L'.

Definition copreserve :=
  forall (G: D ~> S) L, is_colimit G L -> is_colimit (F ∘ G) (cone_whisk_l (cof F) (cof G) L).
End preservation.

Definition fin_continue {S T: Category} (F: S ~> T) :=
  forall D, fin D -> preserve F D.

Definition fin_cocontinue {S T: Category} (F: S ~> T) :=
  forall D, fin D -> copreserve F D.
