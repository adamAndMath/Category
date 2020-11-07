Require Export Sets.FinSet.
Require Export Structure.
Local Open Scope fset.

Definition finset_one: FinSet := single Ø.

Program Definition finset_to_one (X: FinSet): X ~> finset_one := {|
  FinSet.rel := cartisian X finset_one;
|}.
Next Obligation.
  reflexivity.
Qed.
Next Obligation.
  exists Ø; split.
  apply in_cartisian'.
  split.
  exact H.
  now apply in_single.
  intros y Hy.
  apply in_cartisian', proj2 in Hy.
  symmetry.
  now apply in_single.
Qed.

Lemma finset_to_one_unique {X: FinSet} (f: X ~> finset_one): finset_to_one X = f.
Proof.
  apply FinSet.hom_eq.
  split; intros Hp.
  apply in_cartisian' in Hp.
  destruct Hp as [Hx Hy].
  apply in_single in Hy.
  subst y.
  destruct (FinSet.functional _ _ f x Hx) as [y [Hy _]].
  enough (y = Ø).
  now subst y.
  apply FinSet.sign in Hy.
  apply in_cartisian', proj2 in Hy.
  now apply in_single.
  apply FinSet.sign in Hp.
  exact Hp.
Qed.

Definition TopFinSet_mixin: TopCategory.mixin_of FinSet :=
  TopCategory.Mixin FinSet finset_one finset_to_one (@finset_to_one_unique).

Canonical TopFinSet := TopCategory.Pack FinSet TopFinSet_mixin.

Definition finset_zero: FinSet := Ø.

Program Definition finset_from_zero (X: FinSet): finset_zero ~> X := {|
  FinSet.rel := Ø;
|}.
Next Obligation.
  intros x Hx.
  now apply in_empty in Hx.
Qed.
Next Obligation.
  now apply in_empty in H.
Qed.

Lemma finset_from_zero_unique {X: FinSet} (f: finset_zero ~> X): finset_from_zero X = f.
Proof.
  apply FinSet.hom_eq.
  split; intros Hp.
  now apply in_empty in Hp.
  apply FinSet.sign in Hp.
  apply in_cartisian' in Hp.
  destruct Hp as [Hx _].
  now apply in_empty in Hx.
Qed.

Definition BotFinSet_mixin: BotCategory.mixin_of FinSet :=
  BotCategory.Mixin FinSet finset_zero finset_from_zero (@finset_from_zero_unique).

Canonical BotFinSet := BotCategory.Pack FinSet BotFinSet_mixin.

Lemma in_one (x: fset): x ∈ 1 <-> x = 0.
Proof. apply in_single. Qed.

Lemma Fun_to_one {X: FinSet} (x: fset): x ∈ X -> finset_to_one X x = 0.
Proof.
  intros Hx.
  apply FinSet.Fun_unique.
  apply in_cartisian'.
  split.
  exact Hx.
  now apply in_one.
Qed.

Program Definition finset_fork {X Y Z: FinSet} (f: X ~> Y) (g: X ~> Z): X ~> cartisian Y Z :=
  FinSet.homFun (fun x => pair (f x) (g x)) _.
Next Obligation.
  apply in_cartisian'.
  split.
  all: apply FinSet.Fun_to, H.
Qed.

Definition finset_pi1_f (p: fset) := ∪ ∩ p.
Definition finset_pi2_f (p: fset) := (∪ ∪ p) \ (∪ ∩ p) ∪ (∩ ∪ p).

Lemma finset_pi1_correct (x y: fset): finset_pi1_f (pair x y) = x.
Proof.
  unfold finset_pi1_f.
  rewrite intersect_pair, union_single.
  reflexivity.
Qed.

Lemma finset_pi2_correct (x y: fset): finset_pi2_f (pair x y) = y.
Proof.
  unfold finset_pi2_f.
  rewrite union_pair, intersect_pair, union_single.
  apply fset_eq_ext.
  intros z.
  change (∪ {x, y}) with (x ∪ y).
  replace (∩ {x, y}) with (x ∩ y).
  rewrite in_binunion, in_diff.
  rewrite in_binunion, in_binintersect.
  split.
  + intros [[[H | H] n] | [_ H]].
    contradiction.
    all: exact H.
  + intros Hz.
    destruct (classic (z ∈ x)).
    all: [> right | left].
    all: split; try assumption.
    now right.
  + apply fset_eq_ext.
    clear z.
    intros z.
    rewrite in_intersect, in_binintersect.
    setoid_rewrite in_upair.
    2: apply upair_not_empty.
    split.
    intros [Hx Hy] e [H | H].
    1, 2: now subst e.
    intros H.
    split.
    all: apply H.
    now left.
    now right.
Qed.

Program Definition finset_pi1 {A B: fset}: (cartisian A B: fset) ~> A :=
  FinSet.homFun finset_pi1_f _.
Next Obligation.
  apply in_cartisian in H.
  destruct H as [a [b [Ha [Hb H]]]].
  subst x.
  rewrite finset_pi1_correct.
  exact Ha.
Qed.

Program Definition finset_pi2 {A B: fset}: cartisian A B ~> B :=
  FinSet.homFun finset_pi2_f _.
Next Obligation.
  apply in_cartisian in H.
  destruct H as [a [b [Ha [Hb H]]]].
  subst x.
  rewrite finset_pi2_correct.
  exact Hb.
Qed.

Lemma finset_fork_pi {A B C: FinSet} (f: A ~> B) (g: A ~> C) (h: A ~> cartisian B C): h = finset_fork f g <-> finset_pi1 ∘ h = f /\ finset_pi2 ∘ h = g.
Proof.
  split.
  + intros H.
    subst h.
    split.
    all: apply FinSet.hom_ext.
    all: intros a Ha.
    all: rewrite FinSet.Fun_comp by exact Ha.
    all: unfold finset_fork.
    all: rewrite FinSet.Fun_homFun by exact Ha.
    1: unfold finset_pi1.
    2: unfold finset_pi2.
    all: rewrite FinSet.Fun_homFun.
    1: apply finset_pi1_correct.
    2: apply finset_pi2_correct.
    all: apply in_cartisian'.
    all: split.
    all: apply FinSet.Fun_to, Ha.
  + intros [Hf Hg].
    subst f g.
    rename h into f.
    symmetry.
    apply FinSet.hom_ext.
    intros a Ha.
    unfold finset_fork.
    rewrite FinSet.Fun_homFun by exact Ha.
    rewrite !FinSet.Fun_comp by exact Ha.
    unfold finset_pi1, finset_pi2.
    rewrite !FinSet.Fun_homFun by apply FinSet.Fun_to, Ha.
    specialize (FinSet.Fun_to f a Ha) as Hf.
    apply in_cartisian in Hf.
    destruct Hf as [x [y [Hx [Hy Hf]]]].
    rewrite Hf.
    f_equal.
    apply finset_pi1_correct.
    apply finset_pi2_correct.
Qed.

Definition FinSetProd_mixin :=
  ProdCategory.Mixin FinSet cartisian (@finset_fork) (@finset_pi1) (@finset_pi2) (@finset_fork_pi).

Canonical FinSetProd := ProdCategory.Pack FinSet FinSetProd_mixin.

Definition finsum (X Y: fset): fset :=
  {pair 0 x | x ⋴ X} ∪ {pair 1 y | y ⋴ Y}.

Program Definition finset_merge {X Y Z: FinSet} (f: X ~> Z) (g: Y ~> Z): finsum X Y ~> Z :=
  FinSet.homFun (fun p =>
    if dec (0 ∈ finset_pi1_f p) then
      g (finset_pi2_f p)
    else
      f (finset_pi2_f p)
  ) _.
Next Obligation.
  rename x into p.
  apply in_binunion in H.
  rewrite !in_map in H.
  destruct H as [[x [Hx H]] | [y [Hy H]]].
  all: subst p.
  all: rewrite finset_pi1_correct, finset_pi2_correct.
  + destruct (dec (0 ∈ 0)).
    now apply in_empty in f0.
    apply FinSet.Fun_to, Hx.
  + destruct (dec (0 ∈ 1)).
    apply FinSet.Fun_to, Hy.
    destruct n.
    now apply in_one.
Qed.

Program Definition finset_in1 {X Y: FinSet}: X ~> finsum X Y :=
  FinSet.homFun (fun x => pair 0 x) _.
Next Obligation.
  apply in_binunion.
  left.
  apply in_map', H.
Qed.

Program Definition finset_in2 {X Y: FinSet}: Y ~> finsum X Y :=
  FinSet.homFun (fun y => pair 1 y) _.
Next Obligation.
  apply in_binunion.
  right.
  apply in_map', H.
Qed.

Lemma finset_merge_in {A B C: FinSet} (f: A ~> C) (g: B ~> C) (h: finsum A B ~> C): h = finset_merge f g <-> h ∘ finset_in1 = f /\ h ∘ finset_in2 = g.
Proof.
  split.
  1: intros Hh.
  2: intros [Hf Hg].
  1: subst h.
  2: subst f g.
  split.
  all: apply FinSet.hom_ext.
  + intros a Ha.
    rewrite FinSet.Fun_comp by exact Ha.
    unfold finset_merge.
    rewrite FinSet.Fun_homFun by apply FinSet.Fun_to, Ha.
    unfold finset_in1.
    rewrite FinSet.Fun_homFun by exact Ha.
    rewrite finset_pi1_correct, finset_pi2_correct.
    destruct (dec (0 ∈ 0)).
    now apply in_empty in f0.
    reflexivity.
  + intros b Hb.
    rewrite FinSet.Fun_comp by exact Hb.
    unfold finset_merge.
    rewrite FinSet.Fun_homFun by apply FinSet.Fun_to, Hb.
    unfold finset_in2.
    rewrite FinSet.Fun_homFun by exact Hb.
    rewrite finset_pi1_correct, finset_pi2_correct.
    destruct (dec (0 ∈ 1)).
    reflexivity.
    destruct n.
    now apply in_one.
  + intros x Hx.
    unfold finset_merge.
    rewrite FinSet.Fun_homFun by exact Hx.
    apply in_binunion in Hx.
    destruct (dec (0 ∈ finset_pi1_f x)) as [H | H].
    all: destruct Hx.
    all: apply in_map in H0.
    all: destruct H0 as [y [Hy Hx]].
    all: subst x.
    all: rewrite finset_pi1_correct in H.
    now apply in_empty in H.
    3: destruct H.
    3: now apply in_one.
    all: rewrite finset_pi2_correct.
    all: rewrite FinSet.Fun_comp by exact Hy.
    all: f_equal.
    1: unfold finset_in2.
    2: unfold finset_in1.
    all: symmetry.
    all: apply FinSet.Fun_homFun.
    all: exact Hy.
Qed.

Definition FinSetCoprod_mixin: CoprodCategory.mixin_of FinSet :=
  CoprodCategory.Mixin FinSet finsum (@finset_merge) (@finset_in1) (@finset_in2) (@finset_merge_in).

Canonical FinSetCoprod := CoprodCategory.Pack FinSet FinSetCoprod_mixin.

Definition finset_const {X: fset} (x: fset) (Hx: x ∈ X): 1 ~> X := 
  FinSet.homFun (fun _ => x) (fun _ _ => Hx).

Lemma finset_monic_inj {X Y: FinSet} (f: X ~> Y): monic f <-> forall x y, x ∈ X -> y ∈ X -> f x = f y -> x = y.
Proof.
  split.
  + intros Hf x y Hx Hy H.
    rewrite <- ((FinSet.Fun_unique (finset_const x Hx) Ø x)).
    rewrite <- ((FinSet.Fun_unique (finset_const y Hy) Ø y)).
    f_equal.
    apply Hf.
    apply FinSet.hom_ext; simpl.
    intros o Ho.
    apply in_one in Ho.
    subst o.
    rewrite !FinSet.Fun_comp by now apply in_one.
    unfold finset_const.
    rewrite !FinSet.Fun_homFun by now apply in_one.
    exact H.
    all: apply (in_map' 0).
    all: now apply in_one.
  + intros H Z g1 g2 Hg.
    apply FinSet.hom_ext.
    intros z Hz.
    apply H.
    1, 2: apply FinSet.Fun_to, Hz.
    rewrite <- !FinSet.Fun_comp by exact Hz.
    now f_equal.
Qed.

Lemma finset_epic_surj {X Y: FinSet} (f: X ~> Y): epic f <-> forall y, y ∈ Y -> exists x, x ∈ X /\ f x = y.
Proof.
  split.
  + intros Hf y Hy.
    assert (pair 0 0 ∈ (1: FinSet) + 1) as i0.
      apply in_binunion.
      left.
      now apply in_map', in_one.
    assert (pair 1 0 ∈ (1: FinSet) + 1) as i1.
      apply in_binunion.
      right.
      now apply in_map', in_one.
    simpl in i0, i1.
    set (g1 := FinSet.homFun (fun _ => pair 0 0) (fun y (_: y ∈ Y) => i0): Y ~> _).
    set (g2 := FinSet.homFun (fun y => if dec (exists x, x ∈ X /\ f x = y) then pair 0 0 else pair 1 0)
      (fun y (_: y ∈ Y) => if dec (exists x, x ∈ X /\ f x = y) as d return (if d then pair 0 0 else pair 1 0) ∈ _ then i0 else i1)
      : Y ~> _
    ).
    enough (g1 ∘ f = g2 ∘ f).
    apply Hf in H.
    rewrite FinSet.hom_ext in H.
    specialize (H y Hy).
    unfold g1, g2 in H.
    rewrite !FinSet.Fun_homFun in H by exact Hy.
    destruct (dec (exists x : fset, x ∈ X /\ f x = y)).
    exact e.
    apply pair_inj, proj1 in H.
    symmetry in H.
    contradict H.
    apply not_empty.
    exists 0.
    now apply in_one.
    apply FinSet.hom_ext.
    intros x Hx.
    rewrite !FinSet.Fun_comp by exact Hx.
    unfold g1, g2; clear g1 g2.
    rewrite !FinSet.Fun_homFun by apply FinSet.Fun_to, Hx.
    destruct (dec (exists x', x' ∈ X /\ f x' = f x)).
    reflexivity.
    destruct n.
    now exists x.
  + intros H Z g1 g2 Hg.
    rewrite FinSet.hom_ext in Hg.
    apply FinSet.hom_ext.
    intros y Hy.
    specialize (H y Hy).
    destruct H as [x [Hx e]].
    subst y.
    specialize (Hg x Hx).
    now rewrite <- !FinSet.Fun_comp.
Qed.

Lemma finset_monic_split {X Y: FinSet} (f: X ~> Y): X <> Ø -> monic f -> splitmonic f.
Proof.
  intros HX Hf.
  rewrite finset_monic_inj in Hf.
  apply not_empty in HX.
  destruct HX as [x0 Hx0].
  unshelve eexists.
  2: apply FinSet.hom_ext.
  2: intros x Hx.
  2: rewrite FinSet.Fun_id by exact Hx.
  2: rewrite FinSet.Fun_comp by exact Hx.
  unshelve eapply FinSet.homFun.
  3: rewrite FinSet.Fun_homFun by apply FinSet.Fun_to, Hx.
  exact (fun y =>
    if dec (exists x, x ∈ X /\ f x = y) then
      epsilon (inhabits Ø) (fun x => x ∈ X /\ f x = y)
    else x0
  ).
  all: simpl.
  intros y Hy.
  destruct (dec (exists x, x ∈ X /\ f x = y)).
  apply (epsilon_spec (inhabits Ø) (fun x => x ∈ X /\ f x = y)), e.
  exact Hx0.
  destruct (dec (exists x', x' ∈ X /\ f x' = f x)).
  apply Hf.
  1, 3: apply (epsilon_spec (inhabits Ø) (fun x' => x' ∈ X /\ f x' = f x)), e.
  exact Hx.
  destruct n.
  now exists x.
Qed.

Lemma finset_epic_split {X Y: FinSet} (f: X ~> Y): epic f -> splitepic f.
Proof.
  intros Hf.
  rewrite finset_epic_surj in Hf.
  unshelve eexists.
  2: apply FinSet.hom_ext.
  2: intros y Hy.
  2: rewrite FinSet.Fun_id by exact Hy.
  2: rewrite FinSet.Fun_comp by exact Hy.
  unshelve eapply FinSet.homFun.
  exact (fun y => epsilon (inhabits Ø) (fun x => x ∈ X /\ f x = y)).
  2: rewrite FinSet.Fun_homFun by exact Hy.
  intros y Hy.
  simpl.
  all: apply (epsilon_spec (inhabits Ø) (fun x => x ∈ X /\ f x = y)).
  all: apply Hf, Hy.
Qed.

Fixpoint nodup {A} (l: list A): list A :=
  match l with
  | nil => nil
  | x :: l =>
    if dec (List.In x l) then nodup l
    else x :: nodup l
  end%list.

Lemma in_nodup {A} (x: A) (l: list A): List.In x (nodup l) <-> List.In x l.
Proof.
  induction l in x |- *; simpl.
  reflexivity.
  destruct (dec (List.In a l)).
  split.
  intros H.
  right.
  now apply IHl.
  intros [H | H].
  subst a.
  1, 2: now apply IHl.
  simpl.
  now f_equiv.
Qed.

Lemma nodup_correct {A} (l: list A): List.NoDup (nodup l).
Proof.
  induction l; simpl.
  constructor.
  destruct (dec (List.In a l)).
  exact IHl.
  rewrite <- in_nodup in n.
  now constructor.
Qed.

Lemma nodup_idem {A} (l: list A): List.NoDup l -> nodup l = l.
Proof.
  intros H.
  induction l; simpl.
  reflexivity.
  inversion_clear H.
  destruct (dec (List.In a l)).
  contradiction.
  f_equal.
  now apply IHl.
Qed.

Lemma nodup_app {A} (xs ys: list A): (forall x, List.In x xs -> ~List.In x ys) -> nodup (xs ++ ys) = (nodup xs ++ nodup ys)%list.
Proof.
  intros H.
  induction xs; simpl.
  reflexivity.
  destruct (dec (List.In a (xs ++ ys))).
  apply List.in_app_iff in i.
  destruct i.
  destruct (dec (List.In a xs)).
  apply IHxs.
  intros x Hx.
  apply H.
  now right.
  contradiction.
  contradict H0.
  apply H.
  now left.
  destruct (dec (List.In a xs)).
  destruct n.
  apply List.in_app_iff.
  now left.
  simpl.
  f_equal.
  apply IHxs.
  intros x Hx.
  apply H.
  now right.
Qed.

Definition findex_nd (x: fset) := nodup (indexf x).

Lemma in_findex_nd (X x: fset): List.In x (findex_nd X) <-> x ∈ X.
Proof.
  rewrite in_indexf.
  apply in_nodup.
Qed.

Lemma fset_of_findex_nd (X: fset): fset_of (findex_nd X) = X.
Proof.
  apply fset_eq_ext.
  intros z.
  rewrite in_fset_of.
  apply in_findex_nd.
Qed.

Definition fsize (x: fset): nat := length (findex_nd x).

Lemma fsize_incl (X: fset) (l: list fset): List.NoDup l -> (forall x, fIn x X <-> List.In x l) -> fsize X = length l.
Proof.
  intros Hl H.
  apply PeanoNat.Nat.le_partialorder.
  split.
  all: apply List.NoDup_incl_length.
  apply nodup_correct.
  2: exact Hl.
  all: intros x.
  all: rewrite in_findex_nd.
  all: apply H.
Qed.

Lemma monic_fsize (X Y: fset): (exists f: X ~> Y, monic f) <-> fsize X <= fsize Y.
Proof.
  unfold fsize.
  transitivity (
    exists f : fset -> fset,
    (forall x : fset, List.In x (findex_nd X) -> List.In (f x) (findex_nd Y)) /\
    (forall (x y : fset), List.In x (findex_nd X) -> List.In y (findex_nd X) -> f x = f y -> x = y)
  ).
  2: generalize (nodup_correct (indexf X)) (nodup_correct (indexf Y)).
  2: change (nodup (indexf ?X)) with (findex_nd X).
  2: generalize (findex_nd X) (findex_nd Y).
  2: clear X Y; intros xs ys Hxs Hys.
  all: split.
  + intros [f Hf].
    rewrite finset_monic_inj in Hf.
    exists f.
    split.
    intros x.
    rewrite !in_findex_nd.
    apply FinSet.Fun_to.
    intros x y.
    rewrite !in_findex_nd.
    apply Hf.
  + intros [f [Hf H]].
    setoid_rewrite in_findex_nd in Hf.
    setoid_rewrite in_findex_nd in H.
    exists (FinSet.homFun f Hf).
    apply finset_monic_inj.
    intros x y Hx Hy.
    rewrite !FinSet.Fun_homFun by assumption.
    now apply H.
  + intros [f [Hf H]].
    induction xs in ys, Hxs, Hys, Hf, H |- *; simpl in *.
    apply le_0_n.
    transitivity (length (f a :: List.filter (fun x => if dec (f a = x) then false else true) ys)).
    simpl.
    apply le_n_S.
    apply IHxs.
    now inversion_clear Hxs.
    apply List.NoDup_filter, Hys.
    intros x Hx.
    apply List.filter_In.
    split.
    apply Hf.
    now right.
    destruct (dec (f a = f x)).
    apply H in e.
    subst x.
    now inversion_clear Hxs.
    now left.
    now right.
    reflexivity.
    intros x y Hx Hy.
    apply H.
    1, 2: now right.
    apply List.NoDup_incl_length.
    constructor.
    intros Ha.
    apply List.filter_In, proj2 in Ha.
    destruct (dec (f a = f a)).
    discriminate Ha.
    contradiction.
    apply List.NoDup_filter, Hys.
    intros y Hy.
    simpl in Hy.
    destruct Hy as [Hy | Hy].
    subst y.
    apply Hf.
    now left.
    now apply List.filter_In in Hy.
  + intros H.
    induction xs in ys, Hxs, Hys, H |- *; simpl in *.
    now exists (fun x => x).
    destruct ys as [|y ys].
    inversion H.
    simpl in H.
    apply le_S_n in H.
    inversion_clear Hxs.
    inversion_clear Hys.
    specialize (IHxs ys H1 H3 H).
    destruct IHxs as [f [Hf inj]].
    exists (fun x => if dec (x = a) then y else f x).
    split.
    intros x Hx.
    destruct (dec (x = a)).
    now left.
    destruct Hx.
    now destruct n.
    right.
    now apply Hf.
    intros x1 x2 Hx1 Hx2 Hx.
    destruct (dec (x1 = a)).
    subst x1.
    destruct (dec (x2 = a)).
    subst x2.
    reflexivity.
    subst y.
    destruct Hx2.
    now destruct n.
    specialize (Hf x2 H4).
    contradiction.
    destruct Hx1.
    now destruct n.
    destruct (dec (x2 = a)).
    subst a y.
    specialize (Hf x1 H4).
    contradiction.
    destruct Hx2.
    now destruct n0.
    now apply inj.
Qed.

Lemma fsize_iso (X Y: fset): X ≃ Y <-> fsize X = fsize Y.
Proof.
  unfold fsize.
  transitivity (exists f g: fset -> fset, (forall x, List.In x (findex_nd X) -> List.In (f x) (findex_nd Y)) /\ ((forall y, List.In y (findex_nd Y) -> List.In (g y) (findex_nd X))) /\ (forall x, List.In x (findex_nd X) -> g (f x) = x) /\ (forall y, List.In y (findex_nd Y) -> f (g y) = y)).
  2: generalize (nodup_correct (indexf X)) (nodup_correct (indexf Y)).
  2: change (nodup (indexf ?X)) with (findex_nd X).
  2: generalize (findex_nd X) (findex_nd Y).
  2: clear X Y; intros xs ys Hxs Hys.
  all: split.
  + intros [i].
    exists (to i), (to i⁻¹).
    repeat split.
    all: intros x.
    all: rewrite !in_findex_nd.
    all: intros Hx.
    1, 2: apply FinSet.Fun_to, Hx.
    all: rewrite <- FinSet.Fun_comp by exact Hx.
    1: rewrite inv_l.
    2: rewrite inv_r.
    all: apply FinSet.Fun_id, Hx.
  + intros [f [g [Hf [Hg [Hl Hr]]]]].
    setoid_rewrite in_findex_nd in Hf.
    setoid_rewrite in_findex_nd in Hg.
    setoid_rewrite in_findex_nd in Hl.
    setoid_rewrite in_findex_nd in Hr.
    constructor.
    exists (FinSet.homFun f Hf), (FinSet.homFun g Hg).
    all: apply FinSet.hom_ext.
    all: intros x Hx.
    all: rewrite FinSet.Fun_comp, FinSet.Fun_id by exact Hx.
    all: rewrite !FinSet.Fun_homFun.
    1: apply Hl.
    4: apply Hr.
    3, 6: apply FinSet.Fun_to.
    all: exact Hx.
  + intros [f [g [Hf [Hg [Hl Hr]]]]].
    induction xs in ys, Hxs, Hys, Hf,Hg, Hl, Hr |- *.
    destruct ys as [|b ys].
    all: simpl in *.
    reflexivity.
    destruct Hg with b.
    now left.
    transitivity (length (f a :: List.filter (fun x => if dec (f a = x) then false else true) ys)).
    simpl.
    f_equal.
    apply IHxs.
    - now inversion_clear Hxs.
    - apply List.NoDup_filter, Hys.
    - intros x Hx.
      apply List.filter_In.
      split.
      apply Hf.
      now right.
      destruct (dec (f a = f x)).
      apply (f_equal (fun y => g y)) in e.
      rewrite !Hl in e.
      2, 3: now [> right | left].
      subst x.
      now inversion_clear Hxs.
      reflexivity.
    - intros y Hy.
      apply List.filter_In in Hy.
      destruct Hy as [Hy H].
      destruct (dec (f a = y)).
      discriminate H.
      specialize (Hg y Hy).
      destruct Hg.
      destruct n.
      rewrite <- (Hr y Hy).
      now f_equal.
      exact H0.
    - intros x Hx.
      apply Hl.
      now right.
    - intros y Hy.
      apply List.filter_In in Hy.
      now apply Hr.
    - apply PeanoNat.Nat.le_partialorder.
      split.
      all: apply List.NoDup_incl_length.
      constructor.
      intros H.
      apply List.filter_In in H.
      apply proj2 in H.
      now destruct (dec (f a = f a)) in H.
      apply List.NoDup_filter, Hys.
      2: exact Hys.
      all: red; simpl.
      all: intros y Hy.
      destruct Hy as [Hy | Hy].
      subst y.
      apply Hf.
      now left.
      now apply List.filter_In in Hy.
      rewrite List.filter_In.
      destruct (dec (f a = y)).
      all: now [> left | right].
  + intros H.
    induction xs in ys, Hxs, Hys, H |- *.
    all: destruct ys as [| b ys].
    2, 3: discriminate H.
    all: simpl in *.
    now exists (fun x => x), (fun x => x).
    inversion_clear Hxs.
    inversion_clear Hys.
    injection H.
    clear H; intros H.
    specialize (IHxs ys H1 H3 H).
    destruct IHxs as [f [g [Hf [Hg [Hl Hr]]]]].
    exists (fun x => if dec (a = x) then b else f x).
    exists (fun y => if dec (b = y) then a else g y).
    repeat split.
    - intros x Hx.
      destruct (dec (a = x)).
      now left.
      destruct Hx.
      contradiction.
      right.
      now apply Hf.
    - intros y Hy.
      destruct (dec (b = y)).
      now left.
      destruct Hy.
      contradiction.
      right.
      now apply Hg.
    - intros x Hx.
      destruct (dec (b = if dec (a = x) then b else f x)).
      all: destruct (dec (a = x)).
      exact e0.
      destruct Hx.
      contradiction.
      subst b.
      destruct H2.
      now apply Hf.
      contradiction.
      destruct Hx.
      contradiction.
      now apply Hl.
    - intros y Hy.
      destruct (dec (a = if dec (b = y) then a else g y)).
      all: destruct (dec (b = y)).
      exact e0.
      destruct Hy.
      contradiction.
      subst a.
      destruct H0.
      now apply Hg.
      contradiction.
      destruct Hy.
      contradiction.
      now apply Hr.
Qed.

Lemma fsize_0: fsize 0 = 0%nat.
Proof.
  change 0%nat with (@length fset nil).
  apply fsize_incl.
  constructor.
  intros x.
  split; intros Hx.
  apply in_empty in Hx.
  all: contradiction.
Qed.

Lemma fsize_1: fsize 1 = 1%nat.
Proof.
  change 1%nat with (length (Ø :: nil)).
  apply fsize_incl.
  now repeat constructor.
  intros x.
  unfold one; simpl.
  unfold finset_one.
  rewrite in_single.
  split; intros H.
  now left.
  now destruct H.
Qed.

Lemma fsize_sum (X Y: FinSet): fsize (X + Y) = (fsize X + fsize Y)%nat.
Proof.
  unfold fsize at 2 3.
  rewrite <- (List.map_length (@in1 FinSetCoprod X Y) (findex_nd X)).
  rewrite <- (List.map_length (@in2 FinSetCoprod X Y) (findex_nd Y)).
  rewrite <- List.app_length.
  apply fsize_incl.
  apply List_NoDup_app.
  rewrite <- and_assoc.
  split.
  + split.
    all: apply List_NoDup_map.
    all: split.
    1, 3: apply nodup_correct.
    all: intros x y Hx Hy.
    all: rewrite in_findex_nd in Hx, Hy.
    all: unfold in1, in2; simpl.
    all: unfold finset_in1, finset_in2.
    all: rewrite !FinSet.Fun_homFun by assumption.
    all: intros H.
    all: now apply pair_inj in H.
  + intros p H1 H2.
    apply List.in_map_iff in H1.
    apply List.in_map_iff in H2.
    destruct H1 as [x [H1 Hx]].
    destruct H2 as [y [H2 Hy]].
    subst p.
    rewrite in_findex_nd in Hx, Hy.
    unfold in1, in2 in H2; simpl in H2.
    unfold finset_in1, finset_in2 in H2.
    rewrite !FinSet.Fun_homFun in H2 by assumption.
    apply pair_inj, proj1 in H2.
    contradict H2.
    apply not_empty.
    exists 0.
    now apply in_one.
  + intros p.
    unfold "+"; simpl.
    unfold finsum.
    rewrite in_binunion.
    rewrite List.in_app_iff.
    rewrite !in_map, !List.in_map_iff.
    do 2 f_equiv.
    all: intros x.
    all: rewrite and_comm.
    all: rewrite in_findex_nd.
    all: apply iff_and_r.
    all: intros Hx.
    all: unfold in1, in2; simpl.
    all: unfold finset_in1, finset_in2.
    all: rewrite FinSet.Fun_homFun by exact Hx.
    all: easy.
Qed.

Lemma fsize_prod (X Y: FinSet): fsize (X × Y) = (fsize X * fsize Y)%nat.
Proof.
  transitivity (length (List.flat_map (fun x => List.map (pair x) (findex_nd Y)) (findex_nd X))).
  apply fsize_incl.
  apply List_NoDup_flat_map.
  repeat split.
  apply List.NoDup_filter.
  apply nodup_correct.
  intros x Hx.
  apply List_NoDup_map.
  split.
  apply nodup_correct.
  intros y1 y2 _ _ H.
  now apply pair_inj in H.
  intros x1 x2 p _ _ Hp1 Hp2.
  rewrite List.in_map_iff in Hp1, Hp2.
  destruct Hp1 as [y1 [Hp _]].
  subst p.
  destruct Hp2 as [y2 [H _]].
  now apply pair_inj in H.
  intros p.
  rewrite in_cartisian, List.in_flat_map.
  f_equiv; intros x.
  rewrite List.in_map_iff.
  setoid_rewrite in_findex_nd.
  split.
  intros [y [Hx [Hy Hp]]].
  split.
  exact Hx.
  now exists y.
  intros [Hx [y [Hp Hy]]].
  now exists y.
  unfold fsize.
  generalize (findex_nd X) (findex_nd Y).
  clear X Y; intros xs ys.
  induction xs; simpl.
  reflexivity.
  rewrite List.app_length.
  f_equal.
  apply List.map_length.
  exact IHxs.
Qed.
