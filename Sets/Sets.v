Require Export Structure.
Require Export Sets.Basic.

Definition SET_mixin: Category.mixin_of set :=
  Category.Mixin
    set
    (fun X Y: set => {x: set | x ∈ X} -> {y: set | y ∈ Y})
    (fun _ x => x)
    (fun _ _ _ f g x => f (g x))
    (fun _ _ _ _ _ _ _ => eq_refl)
    (fun _ _ _ => eq_refl)
    (fun _ _ _ => eq_refl).

Canonical SET: Category := Category.Pack set SET_mixin.

Definition map {X Y: set} (f: X ~> Y) (x: set): set :=
  match dec (x ∈ X) with
  | left Hx => proj1_sig (f (exist _ x Hx))
  | right _ => Ø
  end.

Theorem mapto {X Y: set} (f: X ~> Y) (x: set): x ∈ X -> map f x ∈ Y.
Proof.
  intros H.
  unfold map.
  destruct (dec (x ∈ X)).
  apply proj2_sig.
  contradiction.
Qed.

Definition setf_of {X Y: set} (map: set -> set) (mapto: forall x, x ∈ X -> map x ∈ Y): X ~> Y :=
  fun p => exist _ (map (proj1_sig p)) (mapto (proj1_sig p) (proj2_sig p)).

Theorem map_ap {X Y: set} (f: X ~> Y) (x: set) (Hx: x ∈ X): map f x = proj1_sig (f (exist _ x Hx)).
Proof.
  unfold map.
  destruct (dec (x ∈ X)).
  do 3 f_equal.
  apply proof_irrelevance.
  contradiction.
Qed.

Theorem setf_eta {X Y: set} (f: X ~> Y): f = setf_of (map f) (mapto f).
Proof.
  extensionality x.
  destruct x as [x Hx].
  apply eq_sig_hprop.
  intro.
  apply proof_irrelevance.
  simpl.
  symmetry.
  apply map_ap.
Qed.

Theorem setf_eq {X Y: set} (f g: X ~> Y): f = g <-> (forall x, x ∈ X -> map f x = map g x).
Proof.
  split.
  intros fg x Hx.
  now subst g.
  intros H.
  rewrite (setf_eta f), (setf_eta g).
  extensionality x.
  apply eq_sig_hprop.
  intro.
  apply proof_irrelevance.
  simpl.
  apply H, proj2_sig.
Qed.

Lemma map_comp {X Y Z: set} (f: Y ~> Z) (g: X ~> Y) (x: set): x ∈ X -> map (f ∘ g) x = map f (map g x).
Proof.
  intros Hx.
  rewrite (map_ap _ _ (mapto g x Hx)).
  rewrite (map_ap _ _ Hx).
  unfold comp; simpl.
  do 2 f_equal.
  apply eq_sig; simpl.
  symmetry.
  apply map_ap.
Qed.

Program Definition set_fork {A B C: set} (f: A ~> B) (g: A ~> C): A ~> cartisian B C :=
  setf_of (fun x => pair (map f x) (map g x)) _.
Next Obligation.
  apply in_cartisian'.
  split.
  all: apply mapto, H.
Qed.

Definition set_pi1_f (p: set) := ∪ ∩ p.
Definition set_pi2_f (p: set) := (∪ ∪ p) \ (∪ ∩ p) ∪ (∩ ∪ p).

Lemma set_pi1_correct (x y: set): set_pi1_f (pair x y) = x.
Proof.
  unfold set_pi1_f.
  rewrite intersect_pair, union_single.
  reflexivity.
Qed.

Lemma set_pi2_correct (x y: set): set_pi2_f (pair x y) = y.
Proof.
  unfold set_pi2_f.
  rewrite union_pair, intersect_pair, union_single.
  apply set_eq_ext.
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
  + apply set_eq_ext.
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

Program Definition set_pi1 {A B: set}: (cartisian A B: set) ~> A :=
  setf_of set_pi1_f _.
Next Obligation.
  apply in_cartisian in H.
  destruct H as [a [b [Ha [Hb H]]]].
  subst x.
  rewrite set_pi1_correct.
  exact Ha.
Qed.

Program Definition set_pi2 {A B: set}: (cartisian A B: set) ~> B :=
  setf_of set_pi2_f _.
Next Obligation.
  apply in_cartisian in H.
  destruct H as [a [b [Ha [Hb H]]]].
  subst x.
  rewrite set_pi2_correct.
  exact Hb.
Qed.

Lemma set_fork_pi (A B C: set) (f: A ~> B) (g: A ~> C) (h: A ~> cartisian B C): h = set_fork f g <-> set_pi1 ∘ h = f /\ set_pi2 ∘ h = g.
Proof.
  split.
  + intros H.
    subst h.
    split.
    all: apply setf_eq.
    all: intros a Ha.
    all: rewrite (map_ap _ _ Ha).
    all: simpl.
    apply set_pi1_correct.
    apply set_pi2_correct.
  + intros [Hf Hg].
    subst f g.
    rename h into f.
    symmetry.
    apply setf_eq.
    intros a Ha.
    rewrite (map_ap _ _ Ha).
    simpl.
    rewrite !map_comp by exact Ha.
    rewrite !(map_ap _ _ (mapto f a Ha)).
    simpl.
    specialize (mapto f a Ha) as Hf.
    apply in_cartisian in Hf.
    destruct Hf as [b [c [Hb [Hc Hf]]]].
    rewrite Hf.
    f_equal.
    apply set_pi1_correct.
    apply set_pi2_correct.
Qed.

Definition setprod_mixin :=
  ProdCategory.Mixin SET cartisian (@set_fork) (@set_pi1) (@set_pi2) set_fork_pi.

Canonical setprod := ProdCategory.Pack SET setprod_mixin.

Definition set_one: set := single Ø.
Program Definition set_to_one {A: set}: A ~> set_one :=
  setf_of (fun _ => Ø) _.
Next Obligation.
  now apply in_single.
Qed.

Lemma set_to_one_unique {A: set} (f: A ~> set_one): set_to_one = f.
Proof.
  apply setf_eq.
  intros x Hx.
  transitivity Ø.
  2: symmetry.
  all: apply in_single.
  all: apply mapto, Hx.
Qed. 

Definition settop_mixin :=
  TopCategory.Mixin SET set_one (@set_to_one) (@set_to_one_unique).

Canonical settop := TopCategory.Pack SET settop_mixin.

Definition set_from_zero {A: set}: Ø ~> A :=
  fun x => False_rect _ (in_empty _ (proj2_sig x)).

Lemma set_from_zero_unique {A: set} (f: Ø ~> A): set_from_zero = f.
Proof.
  apply setf_eq.
  intros x Hx.
  contradict Hx.
  apply in_empty.
Qed.

Definition setbot_mixin :=
  BotCategory.Mixin SET Ø (@set_from_zero) (@set_from_zero_unique).

Canonical setbot := BotCategory.Pack SET setbot_mixin.

Definition sum (X Y: set): set :=
  {pair 0 x | x ⋴ X} ∪ {pair 1 y | y ⋴ Y}.

Program Definition set_merge {X Y Z: set} (f: X ~> Z) (g: Y ~> Z): sum X Y ~> Z :=
  setf_of (fun p =>
    if dec (0 ∈ set_pi1_f p) then
      map g (set_pi2_f p)
    else
      map f (set_pi2_f p)
  ) _.
Next Obligation.
  rename x into p.
  apply in_binunion in H.
  rewrite !in_map in H.
  destruct H as [[x [Hx H]] | [y [Hy H]]].
  all: subst p.
  all: rewrite set_pi1_correct, set_pi2_correct.
  + destruct (dec (0 ∈ 0)).
    now apply in_empty in i.
    apply mapto, Hx.
  + destruct (dec (0 ∈ 1)).
    apply mapto, Hy.
    destruct n.
    now apply in_single.
Qed.

Program Definition set_in1 {X Y: set}: X ~> sum X Y :=
  setf_of (fun x => pair 0 x) _.
Next Obligation.
  apply in_binunion.
  left.
  apply in_map', H.
Qed.

Program Definition set_in2 {X Y: set}: Y ~> sum X Y :=
  setf_of (fun y => pair 1 y) _.
Next Obligation.
  apply in_binunion.
  right.
  apply in_map', H.
Qed.

Lemma set_merge_in {A B C: set} (f: A ~> C) (g: B ~> C) (h: sum A B ~> C): h = set_merge f g <-> h ∘ set_in1 = f /\ h ∘ set_in2 = g.
Proof.
  split.
  1: intros Hh.
  2: intros [Hf Hg].
  1: subst h.
  2: subst f g.
  split.
  all: apply setf_eq.
  + intros a Ha.
    rewrite (map_ap _ _ Ha).
    simpl.
    rewrite set_pi1_correct, set_pi2_correct.
    destruct (dec (0 ∈ 0)).
    now apply in_empty in i.
    reflexivity.
  + intros b Hb.
    rewrite (map_ap _ _ Hb).
    simpl.
    rewrite set_pi1_correct, set_pi2_correct.
    destruct (dec (0 ∈ 1)).
    reflexivity.
    destruct n.
    now apply in_single.
  + intros x Hx.
    rewrite !(map_ap _ _ Hx).
    rewrite <- map_ap.
    simpl.
    apply in_binunion in Hx.
    rewrite !in_map in Hx.
    destruct Hx as [[a [Ha Hx]] | [b [Hb Hx]]].
    all: subst x.
    all: rewrite set_pi1_correct, set_pi2_correct.
    - destruct (dec (0 ∈ 0)).
      now apply in_empty in i.
      rewrite map_comp by exact Ha.
      f_equal.
      symmetry.
      apply (map_ap set_in1 _ Ha).
    - destruct (dec (0 ∈ 1)).
      rewrite map_comp by exact Hb.
      f_equal.
      symmetry.
      apply (map_ap set_in2 _ Hb).
      destruct n.
      now apply in_single.
Qed.

Definition setcoprod_mixin: CoprodCategory.mixin_of SET :=
  CoprodCategory.Mixin SET sum (@set_merge) (@set_in1) (@set_in2) (@set_merge_in).

Canonical setcoprod := CoprodCategory.Pack SET setcoprod_mixin.

Definition functional (X Y: set) (f: set) :=
  forall x, x ∈ X -> exists! y, y ∈ Y /\ pair x y ∈ f.

Definition set_exp (Y X: set): set :=
  { R ⋴ pow (X × Y) | forall x, x ∈ X -> exists! y, pair x y ∈ R }.

Lemma in_set_exp (Y X f: set): f ∈ set_exp Y X <-> functional X Y f /\ f ⊆ X × Y.
Proof.
  split.
  1: intros Hf.
  2: intros [F Hf].
  split.
  + apply in_sep in Hf.
    destruct Hf as [Hf H].
    apply in_pow in Hf.
    intros x Hx.
    specialize (H x Hx).
    destruct H as [y [Hy H]].
    exists y.
    repeat split.
    apply Hf in Hy.
    apply in_cartisian' in Hy.
    apply Hy.
    exact Hy.
    intros z [_ Hz].
    now apply H.
  + apply in_sep in Hf.
    destruct Hf as [Hf _].
    apply in_pow, Hf.
  + apply in_sep.
    split.
    apply in_pow, Hf.
    intros x Hx.
    specialize (F x Hx).
    destruct F as [y [[_ Hy] H]].
    exists y.
    split.
    exact Hy.
    intros z Hz.
    apply H.
    split.
    apply Hf in Hz.
    now apply in_cartisian' in Hz.
    exact Hz.
Qed.

Definition set_incode {X Y: set} (f: X ~> Y): set :=
  ∪ { { pair x y | y ⋴ { y ⋴ Y | map f x = y } } | x ⋴ X }.

Lemma in_set_incode {X Y: set} (f: X ~> Y) (p: set): p ∈ set_incode f <-> exists x, x ∈ X /\ pair x (map f x) = p.
Proof.
  split.
  + intros H.
    apply in_flat_map in H.
    destruct H as [x [Hx H]].
    apply in_map in H.
    destruct H as [y [Hy Hp]].
    apply in_sep in Hy.
    destruct Hy as [_ Hy].
    subst y p.
    now exists x.
  + intros [x [Hx Hp]].
    subst p.
    apply in_flat_map.
    exists x; split.
    exact Hx.
    apply in_map'.
    apply in_sep.
    repeat split.
    apply mapto, Hx.
Qed.

Lemma in_set_incode' {X Y: set} (f: X ~> Y) (x y: set): pair x y ∈ set_incode f <-> x ∈ X /\ map f x = y.
Proof.
  rewrite in_set_incode.
  split.
  + intros [x' [Hx H]].
    apply pair_inj in H.
    destruct H.
    now subst x' y.
  + intros [Hx Hy].
    subst y.
    now exists x.
Qed.

Lemma set_incode_functional {X Y: set} (f: X ~> Y): functional X Y (set_incode f).
Proof.
  intros x Hx.
  exists (map f x).
  repeat split.
  apply mapto, Hx.
  now apply in_set_incode'.
  intros y [Hy H].
  now apply in_set_incode' in H.
Qed.

Lemma set_incode_rel {X Y: set} (f: X ~> Y): set_incode f ⊆ X × Y.
Proof.
  intros p H.
  apply in_set_incode in H.
  destruct H as [x [Hx Hp]].
  subst p.
  apply in_cartisian'.
  split.
  exact Hx.
  apply mapto, Hx.
Qed.

Program Definition set_decode {X Y: set} (f: set) (F: functional X Y f): X ~> Y :=
  setf_of (fun x => epsilon (inhabits Ø) (fun y => y ∈ Y /\ pair x y ∈ f)) _.
Next Obligation.
  apply (epsilon_spec (inhabits Ø) (fun y => y ∈ Y /\ pair x y ∈ f)).
  specialize (F x H).
  destruct F as [y [Hy _]].
  now exists y.
Qed.

Lemma set_decode_to {X Y: set} (f x: set) (F: functional X Y f): x ∈ X -> pair x (map (set_decode f F) x) ∈ f.
Proof.
  intros Hx.
  rewrite (map_ap _ _ Hx).
  simpl.
  apply (epsilon_spec (inhabits Ø) (fun y => y ∈ Y /\ pair x y ∈ f)).
  specialize (F x Hx).
  destruct F as [y [Hy _]].
  now exists y.
Qed.

Lemma set_decode_spec {X Y: set} (f: set) (x y: set) (F: functional X Y f): x ∈ X -> map (set_decode f F) x = y <-> y ∈ Y /\ pair x y ∈ f.
Proof.
  intros Hx.
  split.
  intros Hy.
  subst y.
  split.
  apply mapto, Hx.
  apply set_decode_to, Hx.
  intros [Hy Hf].
  rewrite (map_ap _ _ Hx).
  simpl.
  specialize (F x Hx).
  destruct F as [z [_ Hz]].
  transitivity z.
  symmetry.
  all: apply Hz; clear z Hz.
  apply epsilon_spec.
  now exists y.
  now split.
Qed.

Lemma set_incode_decode {X Y: set} (f: set) (F: functional X Y f): set_incode (set_decode f F) = f ∩ X × Y.
Proof.
  apply set_eq_ext.
  intros p.
  split.
  + intros H.
    apply in_set_incode in H.
    destruct H as [x [Hx Hp]].
    subst p.
    apply in_binintersect.
    split.
    apply set_decode_to, Hx.
    apply in_cartisian'.
    split.
    exact Hx.
    apply mapto, Hx.
  + intros Hp.
    apply in_binintersect in Hp.
    destruct Hp as [Hf Hp].
    apply in_cartisian in Hp.
    destruct Hp as [x [y [Hx [Hy Hp]]]].
    subst p.
    apply in_set_incode'.
    split.
    exact Hx.
    destruct (F x Hx) as [z [_ H]].
    transitivity z.
    symmetry.
    all: apply H.
    all: split.
    apply mapto, Hx.
    apply set_decode_to, Hx.
    exact Hy.
    exact Hf.
Qed.

Lemma set_decode_incode {X Y: set} (f: X ~> Y): set_decode (set_incode f) (set_incode_functional f) = f.
Proof.
  apply setf_eq.
  intros x Hx.
  rewrite (map_ap _ _ Hx).
  simpl.
  assert (exists y : set, y ∈ Y /\ pair x y ∈ set_incode f).
  exists (map (set_decode (set_incode f) (set_incode_functional f)) x).
  split.
  apply mapto, Hx.
  apply set_decode_to, Hx.
  specialize (epsilon_spec (inhabits Ø) (fun y => y ∈ Y /\ pair x y ∈ set_incode f) H) as Hf.
  clear H.
  destruct Hf as [_ Hf].
  now apply in_set_incode' in Hf.
Qed.

Program Definition set_eval {T S}: set_exp T S × S ~> T :=
  fun p =>
    let f := set_pi1_f (proj1_sig p) in
    let x := set_pi2_f (proj1_sig p) in
    @map S T (set_decode f _) x.
Next Obligation.
  apply in_cartisian in H.
  destruct H as [f [x [Hf [Hx Hp]]]].
  subst p.
  rewrite set_pi1_correct.
  apply in_set_exp, Hf.
Qed.
Next Obligation.
  apply mapto.
  apply in_cartisian in H.
  destruct H as [f [x [Hf [Hx Hp]]]].
  subst p.
  rewrite set_pi2_correct.
  exact Hx.
Qed.

Program Definition set_transpose {T S A: set} (f: A × S ~> T): A ~> set_exp T S :=
  setf_of (fun a => { p ⋴ S × T | exists x, pair x (map f (pair a x)) = p}) _.
Next Obligation.
  rename x into a, H into Ha.
  apply in_set_exp.
  split.
  + intros x Hx.
    exists (map f (pair a x)).
    repeat split.
    apply mapto.
    now apply in_cartisian'.
    apply in_sep.
    split.
    apply in_cartisian'.
    split.
    exact Hx.
    apply mapto.
    now apply in_cartisian'.
    now exists x.
    intros y [Hy H].
    apply in_sep in H.
    destruct H as [_ [z H]].
    apply pair_inj in H.
    destruct H.
    now subst z y.
  + intros p H.
    now apply in_sep in H.
Qed.

Lemma set_transpose_ump {T S A: set} (f: A × S ~> T) (g: A ~> set_exp T S): set_eval ∘ (g (×) id S) = f <-> set_transpose f = g.
Proof.
  rewrite !setf_eq.
  split.
  + intros H x Hx.
    rewrite (map_ap _ _ Hx).
    simpl.
    apply set_eq_ext.
    intros p.
    rewrite in_sep.
    split.
    - intros [Hy [y Hp]].
      subst p.
      apply in_cartisian', proj1 in Hy.
      assert (pair x y ∈ A × S) as Hp.
      now apply in_cartisian'.
      specialize (H (pair x y) Hp).
      rewrite (map_ap _ _ Hp) in H.
      simpl in H.
      apply set_decode_spec, proj2 in H.
      rewrite comp_id_l, map_comp in H by exact Hp.
      2: rewrite comp_id_l, map_comp by exact Hp.
      do 2 rewrite (map_ap _ _ Hp) in H.
      2: do 2 rewrite (map_ap _ _ Hp).
      simpl in H.
      2: simpl.
      rewrite !set_pi1_correct, !set_pi2_correct in H.
      2: rewrite !set_pi1_correct, !set_pi2_correct.
      exact H.
      exact Hy.
    - intros Hg.
      specialize (mapto g x Hx) as Hp.
      apply in_set_exp in Hp.
      destruct Hp as [F Hp].
      specialize (Hp p Hg).
      split.
      exact Hp.
      apply in_cartisian in Hp.
      destruct Hp as [y [z [Hy [Hz Hp]]]].
      subst p.
      exists y.
      f_equal.
      assert (pair x y ∈ A × S) as Hp.
      now apply in_cartisian'.
      rewrite <- H by exact Hp.
      rewrite map_comp by exact Hp.
      rewrite (map_ap _ _ Hp).
      simpl.
      rewrite comp_id_l, map_comp by exact Hp.
      rewrite !(map_ap _ _ Hp).
      simpl.
      rewrite set_pi1_correct, set_pi2_correct.
      clear Hp.
      assert (pair (map g x) y ∈ set_exp T S × S) as Hp.
      apply in_cartisian'.
      split.
      apply mapto, Hx.
      exact Hy.
      rewrite (map_ap _ _ Hp).
      simpl.
      apply set_decode_spec.
      now rewrite set_pi2_correct.
      split.
      exact Hz.
      now rewrite set_pi1_correct, set_pi2_correct.
  + intros Hg p Hp.
    rewrite map_comp by exact Hp.
    rewrite (map_ap _ _ Hp).
    simpl.
    rewrite comp_id_l, map_comp by exact Hp.
    do 2 rewrite (map_ap _ _ Hp).
    simpl.
    apply in_cartisian in Hp.
    destruct Hp as [x [y [Hx [Hy Hp]]]].
    subst p.
    rewrite set_pi1_correct, set_pi2_correct.
    assert (pair (map g x) y ∈ set_exp T S × S) as Hp.
    apply in_cartisian'.
    split.
    apply mapto, Hx.
    exact Hy.
    rewrite (map_ap _ _ Hp).
    simpl.
    apply set_decode_spec.
    now rewrite set_pi2_correct.
    split.
    now apply mapto, in_cartisian'.
    rewrite set_pi1_correct, set_pi2_correct.
    clear Hp.
    rewrite <- Hg by exact Hx.
    rewrite (map_ap _ _ Hx).
    simpl.
    apply in_sep.
    split.
    apply in_cartisian'.
    split.
    exact Hy.
    now apply mapto, in_cartisian'.
    now exists y.
Qed.

Definition setexp_mixin: ExpCategory.mixin_of setprod :=
  ExpCategory.Mixin setprod set_exp (@set_eval) (@set_transpose) (@set_transpose_ump).

Canonical setexp := ExpCategory.Pack setprod (ExpCategory.Class SET setprod_mixin setexp_mixin).

Canonical setcart := CartCategory.Pack SET (CartCategory.Class SET settop_mixin setprod_mixin).
Canonical setccc := CCC.Pack SET (CCC.Class SET (CartCategory.class setcart) setexp_mixin).
