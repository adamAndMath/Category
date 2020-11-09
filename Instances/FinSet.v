Require Export Sets.FinSet.
Require Export Structure.
Local Open Scope fset.

Program Definition finset_from_zero (X: FinSet): Ø ~> X := {|
  FinSet.rel := Ø;
|}.
Next Obligation.
  intros x Hx.
  now apply in_empty in Hx.
Qed.
Next Obligation.
  now apply in_empty in H.
Qed.

Lemma finset_from_zero_unique {X: FinSet} (f: Ø ~> X): finset_from_zero X = f.
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
  BotCategory.Mixin FinSet Ø finset_from_zero (@finset_from_zero_unique).

Canonical BotFinSet := BotCategory.Pack FinSet BotFinSet_mixin.

Program Definition finset_to_one (X: FinSet): X ~> single 0 := {|
  FinSet.rel := cartisian X (single 0);
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

Lemma finset_to_one_unique {X: FinSet} (f: X ~> single 0): finset_to_one X = f.
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
  TopCategory.Mixin FinSet (single 0) finset_to_one (@finset_to_one_unique).

Canonical TopFinSet := TopCategory.Pack FinSet TopFinSet_mixin.

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

Lemma in_prod (p X Y: fset): p ∈ X × Y <-> exists x y, x ∈ X /\ y ∈ Y /\ p = pair x y.
Proof. apply in_cartisian. Qed.

Lemma in_prod' (x y X Y: fset): pair x y ∈ X × Y <-> x ∈ X /\ y ∈ Y.
Proof. apply in_cartisian'. Qed.

Lemma Fun_fork {X Y Z: fset} (f: X ~> Y) (g: X ~> Z) x: x ∈ X -> ⟨f, g⟩ x = pair (f x) (g x).
Proof.
  apply (FinSet.Fun_homFun (fun x => pair (f x) (g x))).
Qed.

Lemma Fun_pi1 {X Y: fset} x y: x ∈ X -> y ∈ Y -> (@π₁ _ X Y) (pair x y) = x.
Proof.
  intros Hx Hy.
  unfold π₁; simpl.
  unfold finset_pi1.
  rewrite FinSet.Fun_homFun by now apply in_prod'.
  apply finset_pi1_correct.
Qed.

Lemma Fun_pi2 {X Y: fset} x y: x ∈ X -> y ∈ Y -> (@π₂ _ X Y) (pair x y) = y.
Proof.
  intros Hx Hy.
  unfold π₂; simpl.
  unfold finset_pi2.
  rewrite FinSet.Fun_homFun by now apply in_prod'.
  apply finset_pi2_correct.
Qed.

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

Lemma in_sum (p X Y: fset): p ∈ X + Y <-> exists x, x ∈ X /\ p = pair 0 x \/ x ∈ Y /\ p = pair 1 x.
Proof.
  unfold "+"; simpl.
  unfold finsum.
  rewrite in_binunion, !in_map.
  split.
  + intros [[x [Hx Hp]] | [x [Hx Hp]]].
    all: exists x.
    all: now [> left | right].
  + intros [x [[Hx Hp] | [Hx Hp]]].
    all: [> left | right].
    all: now exists x.
Qed.

Lemma in_sum_l (x X Y: fset): pair 0 x ∈ X + Y <-> x ∈ X.
Proof.
  rewrite in_sum.
  split.
  + intros [x' [[Hx H] | [_ H]]].
    all: apply pair_inj in H.
    all: destruct H.
    now subst x'.
    symmetry in H.
    contradict H.
    apply not_empty.
    exists 0.
    now apply in_one.
  + intros Hx.
    exists x.
    now left.
Qed.

Lemma in_sum_r (y X Y: fset): pair 1 y ∈ X + Y <-> y ∈ Y.
Proof.
  rewrite in_sum.
  split.
  + intros [y' [[_ H] | [Hy H]]].
    all: apply pair_inj in H.
    all: destruct H.
    contradict H.
    apply not_empty.
    exists 0.
    now apply in_one.
    now subst y'.
  + intros Hy.
    exists y.
    now right.
Qed.

Lemma Fun_merge_l {X Y Z: fset} (f: X ~> Z) (g: Y ~> Z) x: x ∈ X -> [f, g] (pair 0 x) = f x.
Proof.
  intros Hx.
  unfold merge; simpl.
  unfold finset_merge.
  rewrite FinSet.Fun_homFun by now apply in_sum_l.
  rewrite finset_pi1_correct, finset_pi2_correct.
  destruct (dec (0 ∈ 0)).
  now apply in_empty in f0.
  reflexivity.
Qed.

Lemma Fun_merge_r {X Y Z: fset} (f: X ~> Z) (g: Y ~> Z) y: y ∈ Y -> [f, g] (pair 1 y) = g y.
Proof.
  intros Hy.
  unfold merge; simpl.
  unfold finset_merge.
  rewrite FinSet.Fun_homFun by now apply in_sum_r.
  rewrite finset_pi1_correct, finset_pi2_correct.
  destruct (dec (0 ∈ 1)).
  reflexivity.
  destruct n.
  now apply in_one.
Qed.

Lemma Fun_in1 {X Y: fset} x: x ∈ X -> @in1 _ X Y x = pair 0 x.
Proof. apply FinSet.Fun_homFun. Qed.

Lemma Fun_in2 {X Y: fset} y: y ∈ Y -> @in2 _ X Y y = pair 1 y.
Proof. apply FinSet.Fun_homFun. Qed.

Definition finset_exp (T S: FinSet): FinSet :=
  { f ⋴ pow (S × T) | forall x, x ∈ S -> exists! y, pair x y ∈ f }.

Program Definition finset_eval (T S: FinSet): finset_exp T S × S ~> T := {|
  FinSet.rel := { p ⋴ finset_exp T S × S × T | exists f x y, pair x y ∈ f /\ pair (pair f x) y = p }
|}.
Next Obligation.
  intros p Hp.
  now apply in_sep in Hp.
Qed.
Next Obligation.
  rename x into p.
  apply in_prod in H.
  destruct H as [f [x [Hf [Hx Hp]]]].
  subst p.
  apply in_sep in Hf.
  destruct Hf as [Hf H].
  generalize (H x Hx).
  change (?P -> ?Q) with (impl P Q).
  f_equiv; intros y.
  apply iff_impl_subrelation.
  apply unique_iff; clear y.
  intros y.
  rewrite in_sep.
  rewrite !in_prod'.
  unfold finset_exp.
  rewrite in_sep.
  split.
  intros Hy.
  repeat split.
  1, 2, 3: assumption.
  apply in_pow in Hf.
  apply Hf in Hy.
  now apply in_prod' in Hy.
  now exists f, x, y.
  intros [_ [f' [x' [y' [Hy Hp]]]]].
  rewrite !pair_inj in Hp.
  destruct Hp as [[Hf' Hx'] Hy'].
  now subst f' x' y'.
Qed.

Program Definition finset_transpose {T S X: FinSet} (f: X × S ~> T): X ~> finset_exp T S :=
  FinSet.homFun (fun x => {p ⋴ S × T | exists y, y ∈ S /\ pair y (f (pair x y)) = p}) _.
Next Obligation.
  apply in_sep.
  split.
  apply in_pow.
  intros p Hp.
  now apply in_sep in Hp.
  intros y Hy.
  exists (f (pair x y)).
  split.
  apply in_sep.
  split.
  apply in_prod'.
  split.
  exact Hy.
  apply FinSet.Fun_to.
  now apply in_prod'.
  now exists y.
  intros z Hp.
  apply in_sep in Hp.
  destruct Hp as [_ [y' [_ Hp]]].
  apply pair_inj in Hp.
  destruct Hp.
  now subst y'.
Qed.

Lemma finset_transpose_ump {T S X: FinSet} (f: X × S ~> T) (g: X ~> finset_exp T S): finset_eval T S ∘ (g (×) id S) = f <-> finset_transpose f = g.
Proof.
  split; intros H.
  + subst f.
    apply FinSet.hom_ext.
    intros x Hx.
    unfold finset_transpose.
    rewrite FinSet.Fun_homFun by exact Hx.
    apply fset_eq_ext.
    intros p.
    rewrite in_sep.
    split.
    intros [_ [y [Hy Hp]]].
    subst p.
    rewrite FinSet.Fun_comp by now apply in_prod'.
    unfold fprod.
    rewrite comp_id_l.
    rewrite Fun_fork by now apply in_prod'.
    rewrite FinSet.Fun_comp by now apply in_prod'.
    rewrite Fun_pi1, Fun_pi2 by assumption.
    apply (FinSet.Fun_to g) in Hx.
    apply in_sep in Hx as H.
    destruct H as [_ H].
    specialize (H y Hy).
    destruct H as [z [Hz _]].
    enough (finset_eval T S (pair (g x) y) = z).
    rewrite H.
    apply Hz.
    apply FinSet.Fun_unique.
    apply in_sep.
    split.
    apply in_prod'.
    split.
    now apply in_prod'.
    apply in_sep, proj1 in Hx.
    apply in_pow in Hx.
    apply Hx in Hz.
    now apply in_prod' in Hz.
    now exists (g x), y, z.
    intros Hp.
    apply (FinSet.Fun_to g) in Hx as H.
    apply in_sep in H.
    destruct H as [H _].
    apply in_pow in H.
    specialize (H p Hp).
    split.
    exact H.
    apply in_prod in H.
    destruct H as [y [z [Hy [Hz e]]]].
    subst p.
    exists y.
    split.
    exact Hy.
    f_equal.
    rewrite FinSet.Fun_comp by now apply in_prod'.
    unfold fprod.
    rewrite comp_id_l.
    rewrite Fun_fork by now apply in_prod'.
    rewrite FinSet.Fun_comp by now apply in_prod'.
    rewrite Fun_pi1, Fun_pi2 by assumption.
    apply FinSet.Fun_unique.
    apply in_sep.
    split.
    apply in_prod'.
    split.
    apply in_prod'.
    split.
    apply FinSet.Fun_to.
    1, 2, 3: assumption.
    now exists (g x), y, z.
  + subst g.
    apply FinSet.hom_ext.
    intros p Hp.
    rewrite FinSet.Fun_comp by exact Hp.
    unfold fprod.
    rewrite comp_id_l.
    rewrite Fun_fork by exact Hp.
    rewrite FinSet.Fun_comp by exact Hp.
    apply in_prod in Hp.
    destruct Hp as [x [y [Hx [Hy Hp]]]].
    subst p.
    rewrite Fun_pi1, Fun_pi2 by assumption.
    unfold finset_transpose.
    rewrite FinSet.Fun_homFun by exact Hx.
    apply FinSet.Fun_unique.
    apply in_sep.
    split.
    apply in_prod'.
    split.
    apply in_prod'.
    split.
    apply in_sep.
    split.
    apply in_pow.
    intros p Hp.
    now apply in_sep in Hp.
    clear y Hy.
    intros y Hy.
    exists (f (pair x y)).
    split.
    apply in_sep.
    split.
    apply in_prod'.
    split.
    exact Hy.
    apply FinSet.Fun_to.
    now apply in_prod'.
    now exists y.
    intros z Hz.
    apply in_sep in Hz.
    destruct Hz as [_ [y' [_ H]]].
    rewrite !pair_inj in H.
    destruct H.
    now subst y'.
    exact Hy.
    apply FinSet.Fun_to.
    now apply in_prod'.
    do 3 eexists.
    split.
    2: reflexivity.
    apply in_sep.
    split.
    apply in_prod'.
    split.
    exact Hy.
    apply FinSet.Fun_to.
    now apply in_prod'.
    now exists y.
Qed.

Definition FinSetExp_mixin: ExpCategory.mixin_of FinSetProd :=
  ExpCategory.Mixin FinSetProd finset_exp finset_eval (@finset_transpose) (@finset_transpose_ump).

Canonical FinSetExp := ExpCategory.Pack FinSet (ExpCategory.Class FinSet FinSetProd_mixin FinSetExp_mixin).

Lemma in_exp (f T S: fset): f ∈ T ^ S <-> f ⊆ S × T /\ forall x, x ∈ S -> exists! y, pair x y ∈ f.
Proof.
  unfold "^"; simpl.
  unfold finset_exp.
  rewrite in_sep.
  f_equiv.
  apply in_pow.
Qed.

Lemma in_exp' {X Y: fset} (f: X ~> Y): f ∈ Y ^ X.
Proof.
  apply in_exp.
  split.
  apply FinSet.sign.
  apply FinSet.functional.
Qed.

Lemma Fun_eval {X Y: fset} (f: X ~> Y) x: x ∈ X -> eval Y X (pair f x) = f x.
Proof.
  intros Hx.
  apply FinSet.Fun_unique.
  apply in_sep.
  split.
  apply in_prod'.
  split.
  apply in_prod'.
  split.
  apply in_exp'.
  exact Hx.
  apply FinSet.Fun_to, Hx.
  exists f, x, (f x).
  split.
  apply FinSet.Fun_spec, Hx.
  reflexivity.
Qed.

Lemma Fun_transpose {X Y Z: fset} (f: X × Y ~> Z) x: x ∈ X -> transpose f x = {p ⋴ Y × Z | exists y, y ∈ Y /\ pair y (f (pair x y)) = p}.
Proof.
  apply (FinSet.Fun_homFun (fun x => {p ⋴ Y × Z | exists y, y ∈ Y /\ pair y (f (pair x y)) = p})).
Qed.

Definition finset_const {X: fset} (x: fset) (Hx: x ∈ X): 1 ~> X := 
  FinSet.homFun (fun _ => x) (fun _ _ => Hx).

Lemma Fun_const {X: fset} (x: fset) (Hx: x ∈ X): finset_const x Hx 0 = x.
Proof.
  apply FinSet.Fun_homFun.
  now apply in_one.
Qed.

Lemma finset_monic_inj {X Y: FinSet} (f: X ~> Y): monic f <-> forall x y, x ∈ X -> y ∈ X -> f x = f y -> x = y.
Proof.
  split.
  + intros Hf x y Hx Hy H.
    rewrite <- (Fun_const x Hx).
    rewrite <- (Fun_const y Hy).
    f_equal.
    apply Hf.
    apply FinSet.hom_ext; simpl.
    intros o Ho.
    apply in_one in Ho.
    subst o.
    rewrite !FinSet.Fun_comp by now apply in_one.
    rewrite !Fun_const.
    exact H.
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
      now apply in_sum_l, in_one.
    assert (pair 1 0 ∈ (1: FinSet) + 1) as i1.
      now apply in_sum_r, in_one.
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

Fixpoint fencode (n: nat): fset :=
  match n with
  | O => 0
  | S n => fencode n ∪ single (fencode n)
  end.

Lemma in_self x: x ∉ x.
Proof.
  induction x using fset_ind.
  intros Hx.
  specialize (H x Hx).
  contradiction.
Qed.

Lemma in_fencode x n: x ∈ fencode n <-> exists m, m < n /\ fencode m = x.
Proof.
  split.
  + intros Hx.
    induction n; simpl in *.
    now apply in_empty in Hx.
    apply in_binunion in Hx.
    destruct Hx as [Hx | Hx].
    specialize (IHn Hx).
    revert IHn.
    change (?P -> ?Q) with (impl P Q).
    f_equiv.
    intros m [Hm H].
    split.
    now right.
    exact H.
    apply in_single in Hx.
    subst x.
    exists n.
    split.
    now red.
    reflexivity.
  + intros [m [Hm Hx]].
    subst x.
    induction n; simpl.
    inversion Hm.
    apply in_binunion.
    apply le_S_n in Hm.
    inversion Hm; clear Hm.
    subst m.
    all: [> right | left].
    now apply in_single.
    subst n; rename m0 into n.
    apply IHn.
    now apply le_n_S.
Qed.

Lemma fencode_inj (n m: nat): fencode n = fencode m -> n = m.
Proof.
  intros H.
  destruct (PeanoNat.Nat.lt_total n m) as [|[|]].
  2: exact H0.
  1: destruct (in_self (fencode n)).
  2: destruct (in_self (fencode m)).
  all: rewrite <- fset_eq_ext in H.
  all: apply H.
  all: apply in_fencode.
  now exists n.
  now exists m.
Qed.

Lemma in_fencode' (n m: nat): fencode n ∈ fencode m <-> n < m.
Proof.
  rewrite in_fencode.
  split.
  + intros [x [H e]].
    apply fencode_inj in e.
    now subst x.
  + intros H.
    now exists n.
Qed.

Lemma fencode_subset (n m: nat): fencode n ⊆ fencode m <-> n <= m.
Proof.
  split.
  + intros H.
    destruct (PeanoNat.Nat.lt_total n m) as [|[|]].
    apply le_S_n.
    now right.
    now subst n.
    destruct (in_self (fencode m)).
    apply H.
    now apply in_fencode'.
  + intros H x.
    change (?P -> ?Q) with (impl P Q).
    rewrite !in_fencode.
    f_equiv.
    intros p.
    f_equiv.
    intros Hp.
    red.
    now rewrite <- H.
Qed.

Lemma fsize_fencode (n: nat): fsize (fencode n) = n.
Proof.
  rewrite <- (List.seq_length n 0) at 2.
  rewrite <- (List.map_length fencode).
  apply fsize_incl.
  + apply List_NoDup_map.
    split.
    apply List.seq_NoDup.
    intros x y _ _.
    apply fencode_inj.
  + intros x.
    rewrite in_fencode.
    rewrite List.in_map_iff.
    f_equiv.
    intros m.
    rewrite and_comm.
    apply iff_and_l.
    intros Hx.
    subst x.
    rewrite List.in_seq.
    split.
    intros H.
    split.
    apply le_0_n.
    exact H.
    easy.
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

Lemma fsize_single x: fsize (single x) = 1%nat.
Proof.
  change 1%nat with (length (x :: nil)).
  apply fsize_incl.
  now repeat constructor.
  intros y.
  rewrite in_single.
  split; intros H.
  now left.
  now destruct H.
Qed.

Lemma fsize_1: fsize 1 = 1%nat.
Proof. apply fsize_single. Qed.

Lemma fsize_map_inj f X: (forall x y, x ∈ X -> y ∈ X -> f x = f y -> x = y) -> fsize { f x | x ⋴ X } = fsize X.
Proof.
  intros H.
  apply fsize_iso.
  symmetry.
  assert (forall x, x ∈ X -> f x ∈ {f x | x ⋴ X}) as Hf.
    intros x.
    apply in_map'.
  apply (@is_isomorphic FinSet _ _ (FinSet.homFun f Hf)).
  apply splitepic_monic.
  apply finset_epic_split.
  apply finset_epic_surj.
  intros y.
  change (?P -> ?Q) with (impl P Q).
  rewrite in_map.
  f_equiv.
  intros x [Hx Hy].
  subst y.
  split.
  exact Hx.
  apply FinSet.Fun_homFun, Hx.
  apply finset_monic_inj.
  intros x y Hx Hy.
  rewrite !FinSet.Fun_homFun by assumption.
  now apply H.
Qed.

Lemma fsize_disjoint_binunion X Y: (forall x, x ∈ X -> x ∉ Y) -> fsize (X ∪ Y) = (fsize X + fsize Y)%nat.
Proof.
  intros H.
  unfold fsize at 2 3.
  rewrite <- List.app_length.
  apply fsize_incl.
  apply List_NoDup_app.
  repeat split.
  1, 2: apply nodup_correct.
  intros x.
  rewrite !in_findex_nd.
  apply H.
  intros x.
  symmetry.
  rewrite in_binunion, List.in_app_iff.
  f_equiv.
  all: apply in_findex_nd.
Qed.

Lemma fsize_flat_map_inj X f: (forall x y e, x ∈ X -> y ∈ X -> e ∈ f x -> e ∈ f y -> x = y) -> fsize (∪ {f x | x ⋴ X}) = List.list_sum (List.map fsize (List.map f (findex_nd X))).
Proof.
  intros H.
  transitivity (fsize (List.fold_right binunion Ø (List.map f (findex_nd X)))).
  clear H.
  f_equiv.
  apply fset_eq_ext.
  intros e.
  rewrite in_union.
  setoid_rewrite in_map.
  setoid_rewrite <- in_findex_nd at 1.
  generalize (findex_nd X).
  clear X; intros xs.
  split.
  1: intros [y [[x [Hx Hy]] He]].
  2: intros He.
  subst y.
  1, 2: induction xs; simpl in *.
  contradiction.
  apply in_binunion.
  destruct Hx; [left | right].
  now subst x.
  apply IHxs, H.
  now apply in_empty in He.
  apply in_binunion in He.
  destruct He as [He | He].
  exists (f a); split.
  exists a; split.
  now left.
  reflexivity.
  exact He.
  apply IHxs in He; clear IHxs.
  destruct He as [y [[x [Hx Hy]] He]].
  exists y; split.
  exists x; split.
  now right.
  exact Hy.
  exact He.
  revert H.
  setoid_rewrite <- in_findex_nd at 1 2.
  generalize (nodup_correct (indexf X)).
  change (nodup (indexf X)) with (findex_nd X).
  generalize (findex_nd X).
  clear X; intros xs Hxs H.
  induction xs; simpl.
  apply fsize_0.
  inversion_clear Hxs.
  rename H0 into Ha, H1 into Hxs.
  rewrite fsize_disjoint_binunion.
  f_equal.
  apply IHxs.
  exact Hxs.
  intros x y e Hx Hy.
  apply H.
  1, 2: now right.
  intros e He.
  simpl in H.
  specialize (fun x Hx => H a x e (or_introl eq_refl) (or_intror Hx) He).
  clear - H Ha.
  induction xs; simpl in *.
  apply in_empty.
  intros Hx.
  apply in_binunion in Hx.
  destruct Hx as [Hx | Hx].
  destruct Ha.
  left.
  symmetry.
  apply H.
  now left.
  exact Hx.
  revert Hx.
  apply IHxs.
  intros x Hx.
  apply H.
  now right.
  contradict Ha.
  now right.
Qed.

Lemma fsize_disjoint_union X: (forall x y e, x ∈ X -> y ∈ X -> e ∈ x -> e ∈ y -> x = y) -> fsize (∪ X) = List.list_sum (List.map fsize (findex_nd X)).
Proof.
  intros H.
  rewrite <- (map_id X) at 1.
  rewrite fsize_flat_map_inj.
  do 2 f_equal.
  apply List.map_id.
  exact H.
Qed.

Lemma fsize_sum (X Y: FinSet): fsize (X + Y) = (fsize X + fsize Y)%nat.
Proof.
  unfold "+"; simpl.
  unfold finsum.
  rewrite fsize_disjoint_binunion.
  f_equiv.
  1, 2: apply fsize_map_inj.
  1, 2: intros x y _ _ H.
  1, 2: now apply pair_inj in H.
  intros p Hx Hy.
  rewrite in_map in Hx, Hy.
  destruct Hx as [x [_ Hx]].
  destruct Hy as [y [_ Hy]].
  subst p.
  apply pair_inj, proj1 in Hy.
  symmetry in Hy.
  apply not_empty in Hy.
  exact Hy.
  exists 0.
  now apply in_one.
Qed.

Lemma fsize_prod (X Y: FinSet): fsize (X × Y) = (fsize X * fsize Y)%nat.
Proof.
  unfold "×"; simpl.
  unfold cartisian.
  rewrite fsize_flat_map_inj.
  unfold fsize at 2.
  generalize (findex_nd X).
  clear X; intros xs.
  induction xs; simpl.
  reflexivity.
  f_equal.
  apply fsize_map_inj.
  intros x y _ _ H.
  now apply pair_inj in H.
  exact IHxs.
  intros x y e Hx Hy Hx' Hy'.
  rewrite in_map in Hx', Hy'.
  destruct Hx' as [p1 [_ He]].
  destruct Hy' as [p2 [_ H]].
  subst e.
  now apply pair_inj in H.
Qed.

Lemma fsize_exp (Y X: FinSet): fsize (Y ^ X) = PeanoNat.Nat.pow (fsize Y) (fsize X).
Proof.
  assert (forall xs, List.NoDup xs -> forall f, (forall p, p ∈ f -> exists x y, List.In x xs /\ y ∈ Y /\ p = pair x y) /\ (forall x, List.In x xs -> exists! y, pair x y ∈ f) <-> f ∈ List.fold_right (fun x r => ∪{{ single (pair x y) ∪ f | f ⋴ r} | y ⋴ Y}) (@one TopFinSet) (xs)).
  clear X.
  intros xs Hxs f.
  split.
  intros [H Hf].
  induction xs in Hxs, f, H, Hf |- *; simpl in *.
  apply in_one.
  apply fset_eq_ext.
  intros z.
  split; intros Hz.
  apply H in Hz.
  destruct Hz as [_ [_ [Hz _]]].
  contradiction.
  now apply in_empty in Hz.
  inversion_clear Hxs.
  rename H0 into Ha, H1 into Hxs.
  specialize (IHxs Hxs).
  destruct (Hf a (or_introl eq_refl)) as [b Hb].
  apply in_flat_map.
  exists b; split.
  specialize (H _ (proj1 Hb)).
  destruct H as [x [y [_ [Hy H]]]].
  apply pair_inj, proj2 in H.
  now subst y.
  apply in_map.
  exists (f \ single (pair a b)).
  split.
  apply IHxs.
  intros p Hp.
  rewrite in_diff, in_single in Hp.
  destruct Hp as [Hp n].
  specialize (H p Hp).
  destruct H as [x [y [Hx [Hy H]]]].
  subst p.
  destruct Hx as [Hx | Hx].
  destruct n.
  subst x.
  f_equal.
  symmetry.
  apply Hb, Hp.
  now exists x, y.
  intros x Hx.
  specialize (Hf x (or_intror Hx)).
  revert Hf.
  apply iff_impl_subrelation.
  do 2 f_equiv.
  intros y.
  rewrite in_diff, in_single.
  split.
  intros Hp.
  split.
  exact Hp.
  intros n.
  apply pair_inj in n.
  destruct n.
  now subst x y.
  now intros [Hp _].
  apply fset_eq_ext.
  intros p.
  rewrite in_binunion, in_diff, in_single.
  split.
  intros Hp.
  destruct (classic (p = pair a b)).
  1, 2: now [> left | right].
  intros [Hp | [Hp _]].
  subst p.
  apply Hb.
  exact Hp.
  intros Hf.
  induction xs in Hxs, f, Hf |- *; simpl in *.
  apply in_one in Hf.
  subst f.
  split.
  intros o Ho.
  now apply in_empty in Ho.
  intros x.
  apply False_ind.
  inversion_clear Hxs.
  rename H into Ha, H0 into Hxs.
  apply in_flat_map in Hf.
  destruct Hf as [b [Hb Hf]].
  apply in_map in Hf.
  destruct Hf as [f' [Hf e]].
  subst f; rename f' into f.
  specialize (IHxs Hxs f Hf).
  clear Hf.
  destruct IHxs as [H Hf].
  split.
  intros p Hp.
  rewrite in_binunion, in_single in Hp.
  destruct Hp as [Hp | Hp].
  subst p.
  exists a, b.
  repeat split.
  now left.
  exact Hb.
  specialize (H p Hp).
  destruct H as [x [y [Hx [Hy e]]]].
  exists x, y.
  repeat split.
  now right.
  exact Hy.
  exact e.
  intros x Hx.
  destruct Hx as [Hx | Hx].
  subst x.
  exists b.
  split.
  rewrite in_binunion, in_single.
  now left.
  intros y Hy.
  rewrite in_binunion, in_single in Hy.
  destruct Hy as [Hy | Hy].
  now apply pair_inj in Hy.
  apply H in Hy.
  destruct Hy as [x [y' [Hx [_ e]]]].
  apply pair_inj, proj1 in e.
  now subst x.
  specialize (Hf x Hx).
  revert Hf.
  apply iff_impl_subrelation.
  do 2 f_equiv.
  intros y.
  rewrite in_binunion, in_single.
  split.
  intros Hy.
  now right.
  intros [Hy | Hy].
  apply pair_inj, proj1 in Hy.
  now subst x.
  exact Hy.
  transitivity (fsize (List.fold_right (fun x r : fset => ∪ {{single (pair x y) ∪ f0 | f0 ⋴ r} | y ⋴ Y}) 1 (findex_nd X))).
  f_equal.
  apply fset_eq_ext.
  intros z.
  rewrite <- H; clear H.
  rewrite in_exp.
  setoid_rewrite in_findex_nd.
  setoid_rewrite <- in_prod.
  reflexivity.
  apply nodup_correct.
  generalize (nodup_correct (indexf X)).
  change (nodup (indexf X)) with (findex_nd X).
  unfold fsize at 3.
  generalize (findex_nd X).
  clear X; intros xs Hxs.
  induction xs; simpl.
  apply fsize_1.
  inversion_clear Hxs.
  rename H0 into Ha, H1 into Hxs.
  specialize (IHxs Hxs).
  specialize (H xs Hxs).
  rewrite fsize_flat_map_inj.
  2: {
    intros x y e Hx Hy Hx' Hy'.
    rewrite in_map in Hx', Hy'.
    destruct Hx' as [f [Hf Hx']].
    destruct Hy' as [g [Hg Hy']].
    subst e.
    rewrite <- fset_eq_ext in Hy'.
    specialize (Hy' (pair a x)).
    apply proj1 in Hy'.
    rewrite !in_binunion, !in_single in Hy'.
    specialize (Hy' (or_introl eq_refl)).
    destruct Hy' as [e | Hp].
    now apply pair_inj in e.
    apply H, proj1 in Hg.
    apply Hg in Hp.
    destruct Hp as [a' [x' [Ha' [_ Hp]]]].
    apply pair_inj, proj1 in Hp.
    now subst a'.
  }
  rewrite List.map_map.
  transitivity (List.list_sum (List.map (fun _ => PeanoNat.Nat.pow (fsize Y) (length xs)) (findex_nd Y))).
  f_equal.
  apply List.map_ext_in.
  intros b Hb.
  rewrite <- IHxs; clear IHxs.
  apply fsize_map_inj.
  intros f g Hf Hg e.
  rewrite <- fset_eq_ext in e |- *.
  intros p.
  specialize (e p).
  rewrite !in_binunion, !in_single in e.
  split; [apply proj1 in e | apply proj2 in e].
  1, 2: intros Hp.
  1, 2: specialize (e (or_intror Hp)).
  1, 2: destruct e as [e | e].
  2, 4: exact e.
  1, 2: subst p.
  1: apply H, proj1 in Hf.
  2: apply H, proj1 in Hg.
  1: apply Hf in Hp.
  2: apply Hg in Hp.
  1, 2: destruct Hp as [x [y [Hx [_ e]]]].
  1, 2: apply pair_inj, proj1 in e.
  1, 2: now subst x.
  unfold fsize at 2.
  generalize (findex_nd Y) (PeanoNat.Nat.pow (fsize Y) (length xs)).
  clear.
  intros l n.
  induction l; simpl.
  reflexivity.
  now f_equal.
Qed.

Module FinOrd.

Structure hom (n m: nat) := Hom {
  repr: list nat;
  repr_from: length repr = n;
  repr_to x: List.In x repr -> x < m;
}.

Arguments repr {n m} _.
Arguments repr_from {n m} _.
Arguments repr_to {n m} _ x H.

Lemma hom_eq {n m} (f g: hom n m): f = g <-> repr f = repr g.
Proof.
  split.
  intros H.
  now subst g.
  destruct f as [f f1 f2], g as [g g1 g2].
  simpl.
  intros H.
  subst g.
  f_equal; apply proof_irrelevance.
Qed.

Lemma hom_ext {n m} (f g: hom n m): f = g <-> forall i, i < n -> List.nth i (repr f) 0%nat = List.nth i (repr g) 0%nat.
Proof.
  split.
  intros H.
  now subst g.
  intros H.
  apply hom_eq.
  apply (List.nth_ext _ _ 0%nat 0%nat).
  all: now rewrite !repr_from.
Qed.

Program Definition id n: hom n n := {|
  repr := List.seq 0 n;
|}.
Next Obligation.
  apply List.seq_length.
Qed.
Next Obligation.
  now apply List.in_seq in H.
Qed.

Program Definition comp {x y z} (f: hom y z) (g: hom x y): hom x z := {|
  repr := List.map (fun x => List.nth x (repr f) 0%nat) (repr g);
|}.
Next Obligation.
  rewrite List.map_length.
  apply repr_from.
Qed.
Next Obligation.
  apply List.in_map_iff in H.
  destruct H as [n [H Hn]].
  subst x0.
  apply (repr_to f).
  apply List.nth_In.
  rewrite repr_from.
  apply (repr_to g), Hn.
Qed.

Lemma comp_assoc {a b c d} (f: hom c d) (g: hom b c) (h: hom a b): comp f (comp g h) = comp (comp f g) h.
Proof.
  apply hom_eq; simpl.
  rewrite List.map_map.
  apply List.map_ext_in.
  intros x Hx.
  symmetry.
  rewrite (List.nth_indep _ _ (List.nth 0 (repr f) 0%nat)).
  apply (List.map_nth (fun x => List.nth x (repr f) 0%nat)).
  rewrite List.map_length, repr_from.
  apply (repr_to h), Hx.
Qed.

Lemma comp_id_l {n m} (f: hom n m): comp (id m) f = f.
Proof.
  apply hom_eq; simpl.
  rewrite <- List.map_id.
  apply List.map_ext_in.
  intros x Hx.
  apply List.seq_nth.
  apply (repr_to f), Hx.
Qed.

Lemma comp_id_r {n m} (f: hom n m): comp f (id n) = f.
Proof.
  apply hom_eq; simpl.
  destruct f as [f H H0]; simpl.
  clear H0.
  subst n.
  induction f.
  reflexivity.
  simpl length.
  rewrite <- List.cons_seq, <- List.seq_shift.
  change (a :: List.map (fun x => List.nth x (a :: f) 0%nat) (List.map S (List.seq 0 (length f))) = a :: f)%list.
  f_equal.
  rewrite List.map_map.
  exact IHf.
Qed.

Definition cat_mixin: Category.mixin_of nat :=
  Category.Mixin nat hom id (@comp) (@comp_assoc) (@comp_id_l) (@comp_id_r).

Definition cat := Category.Pack nat cat_mixin.

End FinOrd.

Notation FinOrd := FinOrd.cat.

Section FinOrdSet.

Program Definition FinOrdSet: FinOrd ~> FinSet := {|
  fobj := fencode;
  fmap X Y f := FinSet.homFun (fun x => fencode (List.nth (fsize x) (FinOrd.repr f) 0%nat)) _;
|}.
Next Obligation.
  rewrite in_fencode in H |- *.
  destruct H as [n [Hn Hx]].
  subst x.
  eexists; split.
  2: reflexivity.
  rewrite fsize_fencode.
  apply (FinOrd.repr_to f).
  apply List.nth_In.
  rewrite FinOrd.repr_from.
  exact Hn.
Qed.
Next Obligation.
  apply FinSet.hom_ext.
  intros x Hx.
  rewrite FinSet.Fun_homFun by exact Hx.
  rewrite FinSet.Fun_id by exact Hx.
  apply in_fencode in Hx.
  destruct Hx as [n [Hn Hx]].
  subst x.
  f_equal.
  rewrite fsize_fencode.
  apply List.seq_nth, Hn.
Qed.
Next Obligation.
  apply FinSet.hom_ext.
  intros x Hx.
  rewrite FinSet.Fun_comp by exact Hx.
  rewrite !FinSet.Fun_homFun.
  3: apply FinSet.Fun_to.
  2, 3, 4: exact Hx.
  f_equal.
  apply in_fencode in Hx.
  destruct Hx as [n [Hn Hx]].
  subst x.
  rewrite !fsize_fencode.
  rewrite List.nth_indep with _ _ _ _ (List.nth 0 (FinOrd.repr f) 0%nat).
  apply (List.map_nth (fun x => List.nth x (FinOrd.repr f) 0%nat)).
  rewrite List.map_length.
  rewrite FinOrd.repr_from.
  exact Hn.
Qed.

Lemma FinOrdSet_full: full FinOrdSet.
Proof.
  intros X Y f.
  unshelve eexists.
  exists (List.map (fun x => fsize (f (fencode x))) (List.seq 0 X)).
  3: apply FinSet.hom_ext.
  3: intros x Hx.
  3: simpl.
  3: rewrite FinSet.Fun_homFun by exact Hx.
  rewrite List.map_length.
  apply List.seq_length.
  intros y Hy.
  apply List.in_map_iff in Hy.
  destruct Hy as [x [Hy Hx]].
  subst y.
  apply List.in_seq, proj2 in Hx.
  simpl in Hx.
  apply in_fencode' in Hx.
  apply (FinSet.Fun_to f) in Hx.
  apply in_fencode in Hx.
  destruct Hx as [y [Hy Hx]].
  rewrite <- Hx.
  now rewrite fsize_fencode.
  apply in_fencode in Hx.
  destruct Hx as [n [Hn Hx]].
  subst x.
  rewrite fsize_fencode.
  rewrite List.nth_indep with _ _ _ _ (fsize (f (fencode 0))).
  rewrite (List.map_nth (fun x => fsize (f (fencode x)))).
  rewrite List.seq_nth by exact Hn.
  simpl.
  apply in_fencode' in Hn.
  apply (FinSet.Fun_to f) in Hn.
  apply in_fencode in Hn.
  destruct Hn as [x [Hx Hn]].
  setoid_rewrite <- Hn.
  f_equal.
  apply fsize_fencode.
  rewrite List.map_length.
  rewrite List.seq_length.
  exact Hn.
Qed.

Lemma FinOrdSet_faithful: faithful FinOrdSet.
Proof.
  intros X Y f g H.
  rewrite FinSet.hom_ext in H.
  apply FinOrd.hom_ext.
  intros i Hi.
  apply in_fencode' in Hi.
  specialize (H (fencode i) Hi).
  simpl in H.
  rewrite !FinSet.Fun_homFun in H by exact Hi.
  rewrite fsize_fencode in H.
  now apply fencode_inj.
Qed.

Lemma FinOrdSet_esurj: esurj FinOrdSet.
Proof.
  intros X.
  exists (fsize X).
  apply fsize_iso.
  apply fsize_fencode.
Qed.

Lemma FinOrdSet_is_equiv: is_equiv FinOrdSet.
  apply is_equiv_alt.
  split.
  apply full_and_faithful.
  split.
  exact FinOrdSet_full.
  exact FinOrdSet_faithful.
  exact FinOrdSet_esurj.
Qed.

Lemma FinOrd_FinSet_equiv: FinOrd ≈ FinSet.
Proof.
  exists FinOrdSet.
  exact FinOrdSet_is_equiv.
Qed.

End FinOrdSet.
