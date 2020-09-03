Require Export Structure.
Require Export Basic.

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

Program Definition set_join {A B C: set} (f: A ~> B) (g: A ~> C): A ~> cartisian B C :=
  setf_of (fun x => pair (map f x) (map g x)) _.
Next Obligation.
  apply in_cartisian.
  exists (map f x), (map g x).
  repeat split.
  apply mapto, H.
  apply mapto, H.
Qed.

Program Definition set_pi1 {A B: set}: (cartisian A B: set) ~> A :=
  setf_of (fun p => ∪ ∩ p) _.
Next Obligation.
  apply in_cartisian in H.
  destruct H as [a [b [Ha [Hb H]]]].
  subst x.
  rewrite intersect_pair.
  rewrite union_single.
  exact Ha.
Qed.

Program Definition set_pi2 {A B: set}: (cartisian A B: set) ~> B :=
  setf_of (fun p => (∪ ∪ p) \ (∪ ∩ p) ∪ (∩ ∪ p)) _.
Next Obligation.
  apply in_cartisian in H.
  destruct H as [a [b [Ha [Hb H]]]].
  subst x.
  rewrite union_pair, intersect_pair.
  rewrite union_single.
  replace (∪ {a, b} \ a ∪ ∩ {a, b}) with b.
  exact Hb.
  apply antisymmetry.
  all: intros z Hz.
  + apply in_binunion.
    destruct (classic (z ∈ a)).
    all: [> right | left].
    apply in_intersect.
    apply upair_not_empty.
    intros x Hx.
    apply in_upair in Hx.
    destruct Hx.
    1, 2: now subst x.
    apply in_diff.
    split.
    2: exact H.
    apply in_union.
    exists b.
    split.
    apply in_upair.
    now right.
    exact Hz.
  + apply in_binunion in Hz.
    destruct Hz as [Hz | Hz].
    - apply in_diff in Hz.
      destruct Hz as [Hz H].
      apply in_union in Hz.
      destruct Hz as [y [Hy Hz]].
      apply in_upair in Hy.
      destruct Hy.
      all: subst y.
      contradiction.
      exact Hz.
    - rewrite in_intersect in Hz.
      2: apply upair_not_empty.
      apply Hz.
      apply in_upair.
      now right.
Qed.

Lemma set_pi1_join (A B C: set) (f: A ~> B) (g: A ~> C): set_pi1 ∘ set_join f g = f.
Proof.
  apply setf_eq.
  intros a Ha.
  rewrite (map_ap _ _ Ha).
  simpl.
  rewrite intersect_pair.
  rewrite union_single.
  reflexivity.
Qed.

Lemma set_pi2_join (A B C: set) (f: A ~> B) (g: A ~> C): set_pi2 ∘ set_join f g = g.
Proof.
  apply setf_eq.
  intros a Ha.
  rewrite (map_ap _ _ Ha).
  simpl.
  rewrite union_pair, intersect_pair.
  rewrite union_single.
  apply set_eq_ext.
  intros z.
  rewrite in_binunion, in_diff.
  rewrite in_union, in_intersect.
  2: apply upair_not_empty.
  setoid_rewrite in_upair.
  split.
  + intros [[[y [[Hy | Hy] Hz]] H] | H].
    1, 2: subst y.
    contradiction.
    exact Hz.
    apply H.
    now right.
  + intros Hz.
    destruct (classic (z ∈ map f a)).
    all: [> right | left].
    intros x [Hx | Hx].
    1, 2: now subst x.
    split.
    exists (map g a).
    split.
    now right.
    exact Hz.
    exact H.
Qed.

Lemma set_join_pi (A B C: set) (f: A ~> cartisian B C): set_join (set_pi1 ∘ f) (set_pi2 ∘ f) = f.
Proof.
  apply setf_eq.
  intros a Ha.
  rewrite (map_ap _ _ Ha).
  simpl.
  do 2 rewrite (map_ap _ _ Ha).
  simpl.
  rewrite <- map_ap.
  specialize (mapto f a Ha) as Hf.
  apply in_cartisian in Hf.
  destruct Hf as [b [c [Hb [Hc Hf]]]].
  rewrite Hf.
  rewrite union_pair, intersect_pair.
  rewrite union_single.
  f_equal.
  apply set_eq_ext.
  intros z.
  rewrite in_binunion, in_diff.
  rewrite in_union, in_intersect.
  2: apply upair_not_empty.
  setoid_rewrite in_upair.
  split.
  + intros [[[y [[Hy | Hy] Hz]] H] | H].
    1, 2: subst y.
    contradiction.
    exact Hz.
    apply H.
    now right.
  + intros Hz.
    destruct (classic (z ∈ b)).
    all: [> right | left].
    intros x [Hx | Hx].
    1, 2: now subst x.
    split.
    exists c.
    split.
    now right.
    exact Hz.
    exact H.
Qed.

Definition setprod_mixin :=
  ProdCategory.Mixin SET cartisian (@set_join) (@set_pi1) (@set_pi2) set_pi1_join set_pi2_join set_join_pi.

Canonical setprod := ProdCategory.Pack SET setprod_mixin.

Definition set_one: set := single Ø.
Program Definition set_to_one {A: set}: A ~> set_one :=
  setf_of (fun _ => Ø) _.
Next Obligation.
  now apply in_single.
Qed.

Lemma set_to_one_comp {A B: set} (f: A ~> B): set_to_one ∘ f = set_to_one.
Proof. now apply setf_eq. Qed.

Lemma set_one_to_one: set_to_one = id set_one.
Proof.
  apply setf_eq.
  intros x Hx.
  rewrite !(map_ap _ _ Hx).
  simpl.
  symmetry.
  apply in_single, Hx.
Qed.

Definition settop_mixin :=
  TopCategory.Mixin SET set_one (@set_to_one) (@set_to_one_comp) set_one_to_one.

Canonical settop := TopCategory.Pack SET settop_mixin.
