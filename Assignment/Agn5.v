Require Export Agn1.
Require Export Categories.Path.
Require Export Categories.Algebra.
Require Export Limit.

Lemma ex1 {C: Category} {F: C ~> C} (L L': Algebra F): is_initial L -> is_initial L' -> exists f: L <~> L', forall g, f = g.
Proof.
  intros H H'.
  destruct (H L') as [f Hf].
  destruct (H' L) as [g _].
  unshelve eexists.
  exists f, g.
  3: intros h.
  3: apply iso_eq, Hf.
  1: clear H'.
  1: specialize (H L).
  1: destruct H as [l H].
  2: clear H.
  2: specialize (H' L').
  2: destruct H' as [l H].
  all: transitivity l.
  1, 3: symmetry.
  all: apply H.
Qed.

(* Need to work on duallity *)
Lemma ex1' {C: Category} {F: C ~> C} (L L': Coalgebra F): is_final L -> is_final L' -> exists f: L <~> L', forall g, f = g.
Proof.
  intros H H'.
  assert (exists C', co C' = C).
    exists (co C).
    apply co_invol.
  destruct H0 as [C'].
  subst C; rename C' into C.
  destruct (fiso_surj (CoFun _ _) F) as [F'].
  subst F; rename F' into F.
  destruct (fiso_surj (algebra_cof F) L) as [X].
  subst L; rename X into L.
  destruct (fiso_surj (algebra_cof F) L') as [X].
  subst L'; rename X into L'.
  simpl in F.
  rewrite <- (is_final_co L) in H.
  rewrite <- (is_final_co L') in H'.
  destruct (ex1 L L' H H') as [f Hf].
  exists (imap (algebra_cof F) (Isomorphism.co_iso f)).
  intros g.
  assert (exists g', imap (algebra_cof F) g' = g).
    destruct L as [L γ], L' as [L' γ'].
    simpl in g.
    exists (imap (algebra_cof F)⁻¹ g).
    now apply iso_eq, Coalgebra.hom_eq.
  destruct H0 as [g'].
  subst g.
  f_equal.
  change (Category.obj (Algebra F)) in L, L'.
  assert (exists g: L <~> L', Isomorphism.co_iso g = g').
    unshelve eexists.
    exists (from g'), (to g').
    apply (inv_l g').
    apply (inv_r g').
    now apply iso_eq.
  destruct H0 as [g].
  subst g'.
  now f_equal.
Qed.

Lemma ex2 {C: Category} {F: C ~> C} (L: Algebra F): is_initial L -> is_iso (Algebra.law L).
Proof.
  intros H.
  set (FL := Algebra.Obj (F L) (fmap F (Algebra.law L))).
  assert (exists f: FL ~> L, Algebra.law L = f).
    unshelve eexists.
    exists (Algebra.law L).
    reflexivity.
    reflexivity.
  destruct H0 as [law Hl].
  destruct (H FL) as [i Hi].
  specialize (H L).
  destruct H as [l H].
  exists i; split.
  etransitivity.
  symmetry.
  exact (Algebra.comm i).
  simpl.
  rewrite <- fmap_comp, <- fmap_id.
  f_equal.
  all: rewrite Hl.
  all: apply (Algebra.hom_eq F (law ∘ i) (id L)).
  all: transitivity l.
  1, 3: symmetry.
  all: apply H.
Qed.

Lemma ex2' {C: Category} {F: C ~> C} (L: Coalgebra F): is_final L -> is_iso (Coalgebra.law L).
Proof.
  intros H.
  assert (exists C', co C' = C).
    exists (co C).
    apply co_invol.
  destruct H0 as [C'].
  subst C; rename C' into C.
  destruct (fiso_surj (CoFun _ _) F) as [F'].
  subst F; rename F' into F.
  simpl in F.
  destruct (fiso_surj (algebra_cof F) L) as [L'].
  subst L; rename L' into L.
  apply is_final_co in H.
  simpl.
  destruct (ex2 L H) as [i [Hl Hr]].
  now exists i.
Qed.

Lemma ex3 X: ~ fixpoint T X.
Proof.
  intros [f].
  apply inv in f.
  specialize (iso_epic f) as Hf.
  destruct f as [f g].
  simpl in Hf; clear g.
  rewrite set_epic in Hf.
  set (C := { x ⋴ X | x ∉ map f x}).
  assert (C ∈ pow X) as HC.
    apply in_pow.
    intros x Hx.
    now apply in_sep in Hx.
  specialize (Hf C HC).
  clear HC.
  destruct Hf as [x [Hx H]].
  destruct (classic (x ∈ map f x)).
  + enough (x ∉ map f x).
    now apply H1.
    setoid_rewrite H in H0.
    now apply in_sep in H0.
  + assert (x ∈ C).
      now apply in_sep.
    rewrite <- H in H1.
    now apply H0.
Qed.

Lemma ex3_1 (L: Algebra T): ~ is_initial L.
Proof.
  intros HL.
  apply (ex3 L).
  apply ex2 in HL.
  apply is_iso_ex in HL.
  destruct HL as [f _].
  now constructor.
Qed.

Lemma ex3_2 (L: Coalgebra T): ~ is_final L.
Proof.
  intros HL.
  apply (ex3 L).
  apply ex2' in HL.
  apply is_iso_ex in HL.
  destruct HL as [f _].
  constructor.
  exact (f⁻¹).
Qed.

Fixpoint rec_obj {C: Category} (F: C ~> C) (x: C) n: C :=
  match n with
  | O => x
  | S n => F (rec_obj F x n)
  end.

Fixpoint rec_arr {C: Category} (F: C ~> C) (o: C) (f: o ~> F o) n: rec_obj F o n ~> rec_obj F o (S n) :=
  match n return rec_obj F o n ~> rec_obj F o (S n) with
  | O => f
  | S n => fmap F (rec_arr F o f n)
  end.

Definition rec_path {C: Category} (F: C ~> C) (o: C) (f: o ~> F o): Future C := {|
  Future.objs := rec_obj F o;
  Future.step := rec_arr F o f;
|}.

Fixpoint rec_alg_tr {C: BotCategory} {F: C ~> C} (A: Algebra F) n: rec_obj F 0 n ~> A :=
  match n return rec_obj F 0 n ~> A with
  | O => ¡
  | S n => Algebra.law A ∘ fmap F (rec_alg_tr A n)
  end.

Program Definition rec_alg {C: BotCategory} {F: C ~> C} (A: Algebra F): Future.pfun (rec_path F 0 ¡) ~> Δ (A: C) := {|
  transform := rec_alg_tr A;
|}.
Next Obligation.
  destruct f as [p H].
  subst y.
  simpl.
  rewrite !comp_id_l.
  induction p; simpl.
  apply comp_id_r.
  rewrite <- IHp; clear IHp.
  rewrite comp_assoc.
  f_equal.
  generalize (p + x)%nat.
  clear x p; intros n.
  induction n; simpl.
  symmetry.
  apply from_zero_unique.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  now do 2 f_equal.
Qed.

Fixpoint corec_arr {C: Category} (F: C ~> C) (o: C) (f: F o ~> o) n: rec_obj F o (S n) ~> rec_obj F o n :=
  match n return rec_obj F o (S n) ~> rec_obj F o n with
  | O => f
  | S n => fmap F (corec_arr F o f n)
  end.

Definition corec_path {C: Category} (F: C ~> C) (o: C) (f: F o ~> o): Past C := {|
  Past.objs := rec_obj F o;
  Past.step := corec_arr F o f;
|}.

Lemma ex4 {C: BotCategory} (F: C ~> C): has_colimit Nat C -> copreserve F Nat -> exists L: Algebra F, is_colimit_obj (rec_path F 0 ¡) L /\ is_initial L.
Proof.
  intros H HF.
  rewrite copreserve_alt in HF.
  specialize (H (rec_path F 0 ¡)).
  apply ex_colimit_alt in H.
  destruct H as [l [η H]].
  specialize (HF _ l η H).
  assert (F ∘ rec_path F 0 ¡ = rec_path F 0 ¡ ∘ Nat.Step) as Hstep.
    change (id (Fun Nat C) (F ∘ rec_path F 0 ¡) = id (Fun Nat C) (rec_path F 0 ¡ ∘ Nat.Step)).
    rewrite <- (inv_r (Future_iso C)).
    unfold comp at 1 3.
    unfold Cat, Cat_mixin, Category.comp, Category.class.
    unfold fobj, fun_comp.
    f_equal.
    apply Future.obj_eq; simpl.
    repeat split.
    intros n e eS.
    rewrite !eq_iso_refl; clear e eS.
    simpl.
    rewrite !comp_id_l, !comp_id_r.
    reflexivity.
  set (ϵ := eq_iso (diag_comp l Nat.Step) ∘ (η |> Nat.Step) ∘ eq_iso Hstep).
  destruct (HF l ϵ) as [γ Hγ].
  exists (Algebra.Obj l γ).
  split; simpl.
  apply is_colimit_obj_alt.
  now exists η.
  assert (
    (fun f: F l ~> l => fmap Δ f ∘ (eq_iso (comp_diag F l) ∘ (F <| η)) = ϵ) =
    (fun f: F l ~> l => forall n, f ∘ fmap F (η n) = η (S n))
  ).
  1: {
    extensionality f.
    apply propositional_extensionality.
    split; intros Hf.
    generalize (proj1 (natural_eq _ _) Hf).
    clear Hf; intros Hf; simpl in Hf.
    intros n.
    2: natural_eq n.
    all: specialize (Hf n).
    all: etransitivity.
    1, 3: etransitivity.
    2, 4: exact Hf.
    symmetry.
    4: symmetry.
    1, 2: f_equal.
    all: rewrite <- comp_id_l.
    3, 4: rewrite <- comp_id_r.
    all: f_equal.
    3, 5: f_equal.
    all: apply is_eq_refl.
    1, 2: apply (transform_is_eq (eq_iso (comp_diag F l))).
    3, 4: apply (transform_is_eq (eq_iso (diag_comp l Nat.Step))).
    5, 6: apply (transform_is_eq (eq_iso Hstep)).
    all: apply eq_iso_is_eq.
  }
  setoid_rewrite H0 in Hγ; clear H0.
  intros A.
  destruct (H A (rec_alg A)) as [f Hf].
  assert (
    (fun f: l ~> A => fmap Δ f ∘ η = rec_alg A) =
    (fun f: l ~> A => forall n, f ∘ η n = rec_alg_tr A n)
  ).
  1: {
    clear f Hf.
    extensionality f.
    apply propositional_extensionality.
    apply (natural_eq (fmap Δ f ∘ η)).
  }
  rewrite H0 in Hf; clear H0.
  destruct (HF A (eq_iso (diag_comp (Algebra.carrier A) Nat.Step) ∘ (rec_alg A |> Nat.Step) ∘ eq_iso Hstep)) as [f' Hf'].
  assert (
    (fun f: F l ~> A =>
      fmap Δ f ∘ (eq_iso (comp_diag F l) ∘ (F <| η)) =
      eq_iso (diag_comp (Algebra.carrier A) Nat.Step) ∘ (rec_alg A |> Nat.Step) ∘ eq_iso Hstep) =
    (fun f: F l ~> A => forall n, f ∘ fmap F (η n) = rec_alg_tr A (S n))
  ).
  1: {
    clear γ Hγ f Hf f' Hf'.
    extensionality f.
    apply propositional_extensionality.
    etransitivity.
    apply natural_eq.
    simpl.
    split; intros Hf n.
    all: specialize (Hf n).
    all: etransitivity.
    1, 3: etransitivity.
    2, 4: exact Hf.
    1: symmetry.
    4: symmetry.
    1, 2: f_equal.
    all: rewrite <- comp_id_l.
    3, 4: rewrite <- comp_id_r.
    all: f_equal.
    3, 5: f_equal.
    all: apply is_eq_refl.
    1, 2: apply (transform_is_eq (eq_iso (comp_diag F l))).
    3, 4: apply (transform_is_eq (eq_iso (diag_comp (Algebra.carrier A) Nat.Step))).
    5, 6: apply (transform_is_eq (eq_iso Hstep)).
    all: apply eq_iso_is_eq.
  }
  setoid_rewrite H0 in Hf'; clear H0.
  assert (f' = f ∘ γ).
    apply Hf'.
    intros n.
    rewrite <- comp_assoc.
    rewrite (proj1 Hγ).
    apply (proj1 Hf (S n)).
  subst f'.
  unshelve eexists.
  exists f.
  2: intros [g Hg].
  2: apply Algebra.hom_eq.
  all: simpl.
  symmetry.
  apply Hf'.
  simpl.
  intros n.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  do 2 f_equal.
  apply Hf.
  simpl in g, Hg.
  apply Hf.
  intros n.
  induction n; simpl.
  symmetry.
  apply from_zero_unique.
  rewrite <- IHn; clear IHn.
  rewrite <- (proj1 Hγ).
  rewrite fmap_comp.
  rewrite !comp_assoc.
  now f_equal.
Qed.

Lemma TopCategory_eq (C D: TopCategory): C = D <-> TopCategory.sort C = D /\ forall e: Category.obj C = D, to (eq_iso e) 1 = 1.
Proof.
  split.
  + intros H.
    subst D.
    repeat split.
    intros e.
    rewrite eq_iso_refl.
    reflexivity.
  + destruct C as [C c], D as [D d].
    simpl.
    intros [HC H].
    subst D.
    f_equal.
    specialize (H eq_refl).
    simpl in H.
    unfold one in H.
    destruct c as [x f Hf], d as [y g Hg].
    simpl in H.
    subst y.
    assert (f = g).
    now extensionality a.
    subst g.
    f_equal.
    apply proof_irrelevance.
Qed.

Lemma CoTopBot (C: TopCategory): CoTop (CoBot C) = C.
  apply TopCategory_eq; simpl; split.
  apply co_invol.
  intros e.
  rewrite eq_iso_refl; clear e.
  reflexivity.
Qed.

Lemma cof_rec_path {C: Category} (F: C ~> C) (o: C) (f: o ~> F o): Past.pfun (corec_path (cof F) o f) = cof (rec_path F o f).
Proof.
  assert (forall x, rec_obj (cof F) o x = rec_obj F o x).
    intros x.
    induction x; simpl.
    reflexivity.
    now f_equal.
  fun_eq x y g.
  apply H.
  assert (H0 = H x) by apply proof_irrelevance.
  assert (H1 = H y) by apply proof_irrelevance.
  subst H0 H1.
  destruct g as [p Hp].
  subst x.
  unfold from; simpl.
  rewrite comp_id_l, comp_id_r.
  induction p; simpl.
  rewrite comp_id_r.
  symmetry.
  apply (comp_id_l (eq_iso (H y))).
  change (@comp C _ _ _ ?f ?g) with (@comp (co C) _ _ _ g f).
  rewrite comp_assoc.
  rewrite IHp; clear IHp.
  rewrite <- !comp_assoc.
  f_equal.
  generalize (p + y)%nat.
  clear p y; intros n.
  assert (forall x, to (eq_iso (H (S x))) = fmap F (eq_iso (H x))).
    intros x.
    apply is_eq_unique.
    2: apply (fmap_is_eq (cof F)).
    1, 2: apply eq_iso_is_eq.
  induction n; simpl.
  rewrite !eq_iso_refl.
  simpl.
  rewrite comp_id_r.
  apply comp_id_l.
  setoid_rewrite (H0 n).
  setoid_rewrite (H0 (S n)).
  setoid_rewrite <- (@fmap_comp _ _ F).
  now f_equal.
Qed.

Lemma ex5 {C: TopCategory} (F: C ~> C): has_limit (co Nat) C -> preserve F (co Nat) -> exists L: Coalgebra F, is_limit_obj (corec_path F 1 !) L /\ is_final L.
Proof.
  assert (exists C': BotCategory, CoTop C' = C).
    exists (CoBot C).
    apply CoTopBot.
  destruct H as [C'].
  subst C; rename C' into C.
  destruct (iso_full Co _ _ F) as [F'].
  subst F; rename F' into F.
  simpl.
  intros H HF.
  apply has_limit_co in H.
  rewrite !co_invol in H.
  apply preserve_co in HF.
  rewrite co_invol in HF.
  change (co (co C)) with ((Co' ∘ Co') C) in HF.
  change (cof (cof F)) with (fmap (Co' ∘ Co') F) in HF.
  rewrite Co'_invol in HF.
  simpl in HF.
  destruct (ex4 F H HF) as [L [HL H']].
  clear H HF; rename H' into H.
  exists (to (algebra_cof F) L).
  split.
  rewrite cof_rec_path.
  setoid_rewrite is_limit_obj_co'.
  exact HL.
  apply is_final_co, H.
Qed.
