Require Export Base.

Inductive Acz :=
  acz_of: forall A: Type, (A -> Acz) -> Acz.

Fixpoint acz_eq (A B: Acz): Prop :=
  match A, B with
  | acz_of A f, acz_of B g =>
    (forall a, exists b, acz_eq (f a) (g b)) /\
    (forall b, exists a, acz_eq (f a) (g b))
  end.

Instance acz_equiv: Equivalence acz_eq.
Proof.
  constructor.
  + intros A.
    induction A as [A f IH]; simpl.
    split.
    all: intro a.
    all: exists a.
    all: apply IH.
  + intros A.
    induction A as [A f IH].
    intros [B g] [Hl Hr].
    split.
    1: clear Hl; rename Hr into H.
    2: clear Hr; rename Hl into H.
    all: intros a.
    all: specialize (H a).
    all: destruct H as [b H].
    all: exists b.
    all: apply IH, H.
  + intros A.
    induction A as [A f IH].
    intros [B g] [C h] [AB BA] [BC CB].
    split.
    1: clear BA CB.
    2: clear AB BC; rename BA into BC, CB into AB.
    all: intros a.
    all: specialize (AB a).
    all: destruct AB as [b AB].
    all: specialize (BC b).
    all: destruct BC as [c BC].
    all: exists c.
    all: now apply (IH _ (g b)).
Qed.

Definition acz_in (x X: Acz): Prop :=
  match X with
  | acz_of X f => exists a, acz_eq x (f a)
  end.

Instance acz_in_morph: Proper (acz_eq ==> acz_eq ==> iff) acz_in.
Proof.
  intros x y xy [X f] [Y g] [XY YX].
  simpl.
  split.
  all: intros [a H].
  specialize (XY a).
  destruct XY as [b XY].
  exists b.
  now rewrite <- xy, <- XY.
  specialize (YX a).
  destruct YX as [b YX].
  exists b.
  now rewrite xy, YX.
Qed.

Definition sub_acz (X Y: Acz): Prop :=
  forall z, acz_in z X -> acz_in z Y.

Instance sub_acz_preorder: PreOrder sub_acz.
Proof.
  constructor.
  easy.
  intros X Y Z XY YZ x H.
  apply YZ, XY, H.
Qed.

Instance sub_acz_partialorder: PartialOrder acz_eq sub_acz.
Proof.
  intros [X f] [Y g].
  split; intros [XY YX].
  + split.
    all: intros z [a H].
    1: clear YX.
    2: clear XY; rename YX into XY.
    all: specialize (XY a).
    all: destruct XY as [b XY].
    all: exists b.
    all: now rewrite H.
  + split.
    1: clear YX.
    2: clear XY; rename YX into XY.
    all: intros a.
    1: specialize (XY (f a)).
    2: specialize (XY (g a)).
    all: destruct XY as [b XY].
    1, 3: now exists a.
    all: now exists b.
Qed.

Lemma ain_ind (P: Acz -> Prop):
  Proper (acz_eq ==> iff) P ->
  (forall X, (forall x, acz_in x X -> P x) -> P X) ->
  forall X, P X.
Proof.
  intros morph IH X.
  induction X as [A f H].
  apply IH.
  intros x [a Hx].
  rewrite Hx.
  apply H.
Qed.

Definition acz_empty: Acz := acz_of False (False_rect _).

Definition ɛ_acz: (Acz -> Prop) -> Acz :=
  epsilon (inhabits acz_empty).

Lemma ɛ_acz_correct (P: Acz -> Prop): (exists x, P x) -> P (ɛ_acz P).
Proof. apply epsilon_spec. Qed.

Instance ɛ_acz_ext: Proper (pointwise_relation _ iff ==> eq) ɛ_acz.
Proof.
  intros P Q H.
  f_equal.
  extensionality x.
  apply propositional_extensionality, H.
Qed.

Definition N (X: Acz): Acz := ɛ_acz (acz_eq X).

Lemma acz_eq_N (X: Acz): acz_eq X (N X).
Proof.
  unfold N.
  apply ɛ_acz_correct.
  now exists X.
Qed.

Lemma N_idem (X: Acz): N (N X) = N X.
Proof.
  apply ɛ_acz_ext.
  intros Y.
  split; intro H.
  all: rewrite <- H.
  2: symmetry.
  all: apply acz_eq_N.
Qed.

Lemma acz_N_eq (X Y: Acz): acz_eq X Y <-> N X = N Y.
Proof.
  split.
  + intros H.
    apply ɛ_acz_ext.
    intro x.
    now rewrite H.
  + intros H.
    rewrite acz_eq_N, H.
    symmetry.
    apply acz_eq_N.
Qed.

Structure set: Type := acz_set {
  set_acz: {X | N X = X};
}.

Definition NS (X: Acz): set := acz_set (exist _ (N X) (N_idem X)).

Lemma acz_eq_NS (X: Acz): acz_eq X (proj1_sig (set_acz (NS X))).
Proof. apply acz_eq_N. Qed.

Definition In (X Y: set): Prop := acz_in (proj1_sig (set_acz X)) (proj1_sig (set_acz Y)).

Infix "∈" := In (at level 70).
Notation "x ∉ X" := (~In x X) (at level 70).

Lemma acz_in_set (X Y: set): acz_in (proj1_sig (set_acz X)) (proj1_sig (set_acz Y)) -> X ∈ Y.
Proof. intro H. exact H. Qed.

Lemma acz_in_NS (X Y: Acz): acz_in X Y -> NS X ∈ NS Y.
Proof.
  intro H.
  apply acz_in_set.
  simpl.
  rewrite <- !acz_eq_N.
  exact H.
Qed.

Definition subset (X Y: set): Prop :=
  forall z, z ∈ X -> z ∈ Y.

Infix "⊆" := subset (at level 70).

Instance subset_preorder: PreOrder subset.
Proof.
  constructor.
  easy.
  intros X Y Z XY YZ x H.
  apply YZ, XY, H.
Qed.

Theorem subset_subacz (X Y: set): sub_acz (proj1_sig (set_acz X)) (proj1_sig (set_acz Y)) -> X ⊆ Y.
Proof.
  intros XY z zX.
  apply XY, zX.
Qed.

Instance subset_partialorder: PartialOrder eq subset.
Proof.
  intros X Y.
  split.
  intros H.
  subst Y.
  split; reflexivity.
  intros [XY YX].
  destruct X as [[x Hx]], Y as [[y Hy]].
  f_equal.
  enough (x = y).
  subst y.
  f_equal.
  apply proof_irrelevance.
  rewrite <- Hx, <- Hy.
  apply acz_N_eq.
  apply antisymmetry.
  1: clear YX.
  2: clear XY; rename YX into XY.
  all: intros a H.
  all: rewrite acz_eq_N in H |- *.
  all: exact (XY (NS a) H).
Qed.

Theorem set_eq_ext (X Y: set): (forall z, z ∈ X <-> z ∈ Y) <-> X = Y.
Proof.
  split.
  intros H.
  apply antisymmetry.
  1, 2: intro z.
  1, 2: apply H.
  intros H z.
  now subst Y.
Qed.

Theorem set_acz_eq (X Y: set): acz_eq (proj1_sig (set_acz X)) (proj1_sig (set_acz Y)) -> X = Y.
Proof.
  intros H.
  apply partial_order_equivalence in H.
  destruct H as [XY YX].
  apply antisymmetry.
  all: now apply subset_subacz.
Qed.

Definition index (X: set): { T: Type & T -> set } :=
  match proj1_sig (set_acz X) with
  | acz_of T f => existT _ T (fun a: T => NS (f a))
  end.

Definition set_of (T: Type) (f: T -> set): set :=
  acz_set (exist _ (N (acz_of T (fun a => proj1_sig (set_acz(f a))))) (N_idem _)).

Lemma set_of_index (X: set): set_of (projT1 (index X)) (projT2 (index X)) = X.
Proof.
  apply set_acz_eq.
  unfold index; simpl.
  generalize (proj1_sig (set_acz X)).
  clear X; intros [X f].
  simpl.
  rewrite <- acz_eq_N.
  split.
  all: intros a.
  all: exists a.
  all: symmetry.
  all: apply acz_eq_N.
Qed.

Theorem in_set_of x T (f: T -> set): x ∈ set_of T f <-> exists a: T, x = f a.
Proof.
  unfold In.
  simpl.
  rewrite <- acz_eq_N.
  unfold acz_in.
  f_equiv; intro a.
  split.
  apply set_acz_eq.
  intro H.
  now subst x.
Qed.

Theorem in_index (x X: set): x ∈ X <-> exists a: projT1 (index X), x = projT2 (index X) a.
Proof.
  rewrite <- (set_of_index X) at 1.
  apply in_set_of.
Qed.

Lemma set_NS (X: set): exists x: Acz, X = NS x.
Proof.
  destruct X as [[X H]].
  exists X.
  apply set_acz_eq, acz_eq_N.
Qed.

Lemma set_ind (P: set -> Prop):
  (forall X, (forall x, x ∈ X -> P x) -> P X) ->
  forall X, P X.
Proof.
  intros IH X.
  destruct (set_NS X) as [x H].
  subst X.
  revert x.
  apply ain_ind.
  intros X Y XY.
  f_equiv.
  apply set_acz_eq.
  simpl.
  rewrite <- !acz_eq_N.
  exact XY.
  intros X H.
  apply IH.
  intros Y Hx.
  destruct (set_NS Y) as [x H0].
  subst Y.
  apply H.
  rewrite (acz_eq_N x).
  rewrite (acz_eq_N X).
  exact Hx.
Qed.

Definition empty: set := set_of False (False_rect _).
Notation Ø := empty.

Theorem in_empty (x: set): x ∉ Ø.
Proof.
  intro H.
  apply in_set_of in H.
  destruct H as [F _].
  exact F.
Qed.

Theorem not_empty (x: set): x <> Ø <-> exists z, z ∈ x.
Proof.
  split.
  + intros H.
    destruct (dec (forall z, z ∉ x)).
    destruct H.
    symmetry.
    apply antisymmetry.
    1, 2: intros z Hz.
    now apply in_empty in Hz.
    now specialize (n z).
    destruct (dec (exists z, z ∈ x)).
    exact e.
    destruct n.
    intros z Hz.
    destruct n0.
    now exists z.
  + intros [z Hz] H.
    subst x.
    now apply in_empty in Hz.
Qed.

Definition single (x: set): set :=
  set_of True (fun _ => x).

Theorem in_single (z x: set): z ∈ single x <-> z = x.
Proof.
  unfold single.
  rewrite in_set_of.
  split.
  now intros [_ H].
  intros H.
  now exists I.
Qed.

Theorem single_inj (x y: set): single x = single y <-> x = y.
Proof.
  symmetry.
  split.
  all: intros H.
  now subst y.
  rewrite <- set_eq_ext in H.
  specialize H with x.
  rewrite !in_single in H.
  apply proj1 in H.
  now apply H.
Qed.

Theorem single_not_empty (x: set): single x <> Ø.
Proof.
  apply not_empty.
  exists x.
  now apply in_single.
Qed.

Definition upair (X Y: set): set :=
  set_of bool (fun b => if b then X else Y).

Notation "{ x , y }" := (upair x y) (at level 0, x at level 99, y at level 99).

Theorem in_upair (z x y: set): z ∈ {x, y} <-> z = x \/ z = y.
Proof.
  unfold upair.
  rewrite in_set_of.
  split.
  + intros [[] H].
    now left.
    now right.
  + intros [H | H].
    now exists true.
    now exists false.
Qed.

Lemma upair_not_empty (x y: set): upair x y <> Ø.
Proof.
  apply not_empty.
  exists x.
  apply in_upair.
  now left.
Qed.

Lemma upair_refl (x: set): upair x x = single x.
Proof.
  apply set_eq_ext.
  intros z.
  rewrite in_upair, in_single.
  split.
  now intros [H | H].
  intros H.
  now left.
Qed.

Definition union (X: set): set :=
  set_of { a: projT1 (index X) & projT1 (index (projT2 (index X) a))}
  (fun p => projT2 (index (projT2 (index X) (projT1 p))) (projT2 p)).

Notation "∪ X" := (union X) (at level 40).

Theorem in_union (x X: set): x ∈ ∪ X <-> exists y, y ∈ X /\ x ∈ y.
Proof.
  unfold union.
  rewrite in_set_of.
  split.
  + intros [[a b] H].
    simpl in *.
    subst x.
    exists (projT2 (index X) a).
    split.
    all: apply in_index.
    now exists a.
    now exists b.
  + intros [y [yX xy]].
    apply in_index in yX.
    destruct yX as [a Ha].
    subst y.
    apply in_index in xy.
    destruct xy as [b Hb].
    subst x.
    now exists (existT _ a b).
Qed.

Definition union_single (x: set): ∪ (single x) = x.
Proof.
  apply set_eq_ext.
  intros z.
  rewrite in_union.
  setoid_rewrite in_single.
  split.
  + intros [y [Hy Hz]].
    now subst y.
  + intros Hz.
    now exists x.
Qed.

Definition map (f: set -> set) (X: set): set :=
  set_of (projT1 (index X)) (fun a => f (projT2 (index X) a)).

Notation "{ y | x ⋴ X }" := (map (fun x => y) X) (at level 0, y at level 99, x, X at level 89).

Lemma in_map (z: set) (f: set -> set) (X: set): z ∈ { f x | x ⋴ X } <-> exists x, x ∈ X /\ z = f x.
Proof.
  unfold map.
  rewrite in_set_of.
  split.
  + intros [a H].
    subst z.
    exists (projT2 (index X) a).
    split.
    apply in_index.
    now exists a.
    reflexivity.
  + intros [x [xX Hx]].
    subst z.
    apply in_index in xX.
    destruct xX as [a Ha].
    subst x.
    now exists a.
Qed.

Lemma in_map' (z: set) (f: set -> set) (X: set): z ∈ X -> f z ∈ { f x | x ⋴ X}.
Proof.
  intros Hz.
  apply in_map.
  now exists z.
Qed.

Lemma map_id (X: set): {x | x ⋴ X} = X.
Proof.
  apply set_eq_ext.
  intros z.
  rewrite in_map.
  split.
  intros [x [Hx Hz]].
  now subst z.
  intros Hz.
  now exists z.
Qed.

Lemma map_comp (f g: set -> set) (X: set): {f y | y ⋴ {g x | x ⋴ X}} = {f (g x) | x ⋴ X}.
Proof.
  apply antisymmetry.
  + intros z Hz.
    apply in_map in Hz.
    destruct Hz as [y [Hy Hf]].
    apply in_map in Hy.
    destruct Hy as [x [Hx Hg]].
    subst y z.
    apply (in_map' x), Hx.
  + intros z Hz.
    apply in_map in Hz.
    destruct Hz as [x [Hx Hz]].
    subst z.
    apply in_map'.
    apply in_map'.
    exact Hx.
Qed.

Lemma map_single (f: set -> set) (x: set): {f x | x ⋴ single x} = single (f x).
Proof.
  apply set_eq_ext.
  intros z.
  rewrite in_map.
  setoid_rewrite in_single.
  split.
  + intros [y [Hy Hz]].
    now subst y.
  + intros H.
    now exists x.
Qed.

Lemma in_flat_map (z: set) (f: set -> set) (X: set): z ∈ ∪ {f x | x ⋴ X} <-> exists y, y ∈ X /\ z ∈ f y.
Proof.
  split.
  + intros Hz.
    apply in_union in Hz.
    destruct Hz as [v [Hv Hz]].
    apply in_map in Hv.
    destruct Hv as [y [Hy Hv]].
    subst v.
    now exists y.
  + intros [y [Hy Hz]].
    apply in_union.
    exists (f y).
    split.
    apply in_map.
    now exists y.
    exact Hz.
Qed.

Definition sep (P: set -> Prop) (X: set): set :=
  set_of { a: projT1 (index X) | P (projT2 (index X) a) }
  (fun a => projT2 (index X) (proj1_sig a)).

Notation "{ x ⋴ X | P }" := (sep (fun x => P) X) (at level 0, x, X at level 99, P at level 99).

Lemma in_sep (z: set) (P: set -> Prop) (X: set): z ∈ { x ⋴ X | P x } <-> z ∈ X /\ P z.
Proof.
  unfold sep.
  rewrite in_set_of.
  split.
  + intros [[a Pa] H].
    simpl in *.
    subst z.
    split.
    apply in_index.
    now exists a.
    exact Pa.
  + intros [zX Pz].
    apply in_index in zX.
    destruct zX as [a Ha].
    subst z.
    now exists (exist _ a Pz).
Qed.

Definition intersect (X: set) :=
  { x ⋴ ∪ X | forall y, y ∈ X -> x ∈ y}.

Notation "∩ X" := (intersect X) (at level 40).

Lemma in_intersect (z X: set): X <> Ø -> z ∈ ∩ X <-> forall x, x ∈ X -> z ∈ x.
Proof.
  intros HX.
  unfold intersect.
  rewrite in_sep, in_union.
  split.
  now intros [_ H].
  intros Hz.
  split.
  destruct (dec (forall x, x ∉ X)).
  destruct HX.
  apply antisymmetry.
  1, 2: intros x Hx.
  now specialize (n x).
  now apply in_empty in Hx.
  destruct (dec (exists x, x ∈ X)).
  destruct e as [x Hx].
  exists x.
  split.
  exact Hx.
  apply Hz, Hx.
  destruct n.
  intros x Hx.
  destruct n0.
  now exists x.
  exact Hz.
Qed.

Lemma intersect_single (x: set): ∩ single x = x.
Proof.
  apply set_eq_ext.
  intros z.
  rewrite in_intersect.
  2: apply single_not_empty.
  split; intros Hz.
  + now apply Hz, in_single.
  + intros y Hy.
    apply in_single in Hy.
    now subst y.
Qed.

Definition binunion (x y: set) := ∪ {x, y}.
Infix "∪" := binunion (at level 50, left associativity).

Lemma in_binunion (z x y: set): z ∈ x ∪ y <-> z ∈ x \/ z ∈ y.
Proof.
  unfold binunion.
  rewrite in_union.
  setoid_rewrite in_upair.
  split.
  + intros [p [[Hp | Hp] Hz]].
    all: subst p.
    now left.
    now right.
  + intros [Hz | Hz].
    1: exists x.
    2: exists y.
    all: split.
    2, 4: exact Hz.
    now left.
    now right.
Qed.

Definition binintersect (X Y: set) := {x ⋴ X | x ∈ Y}.
Infix "∩" := binintersect (at level 50, left associativity).

Lemma in_binintersect (z x y: set): z ∈ x ∩ y <-> z ∈ x /\ z ∈ y.
Proof.
  unfold binintersect.
  rewrite in_sep.
  reflexivity.
Qed.

Definition diff (X Y: set) := {x ⋴ X | x ∉ Y}.
Infix "\" := diff (at level 50, left associativity).

Lemma in_diff (z X Y: set): z ∈ X \ Y <-> z ∈ X /\ z ∉ Y.
Proof.
  unfold diff.
  rewrite in_sep.
  reflexivity.
Qed.

Definition pow (X: set): set :=
  set_of (projT1 (index X) -> Prop) (fun P => set_of (sig P) (fun p => projT2 (index X) (proj1_sig p))).

Lemma in_pow (z X: set): z ∈ pow X <-> z ⊆ X.
Proof.
  unfold pow.
  rewrite in_set_of.
  split.
  + intros [P H].
    subst z.
    intros z H.
    apply in_set_of in H.
    destruct H as [[a Pa] H].
    subst z.
    apply in_index.
    now exists a.
  + intros H.
    exists (fun a => projT2 (index X) a ∈ z).
    apply antisymmetry.
    - intros x Hx.
      apply in_set_of.
      specialize (H x Hx).
      apply in_index in H.
      destruct H as [a H].
      subst x.
      now exists (exist _ a Hx).
    - intros x Hx.
      apply in_set_of in Hx.
      destruct Hx as [[a Ha] Hx].
      subst x.
      exact Ha.
Qed.

Definition pair (x y: set): set :=
  { single x, { x, y } }.

Lemma in_pair (z x y: set): z ∈ pair x y <-> z = single x \/ z = {x, y}.
Proof. apply in_upair. Qed.

Lemma pair_not_empty (x y: set): pair x y <> Ø.
Proof. apply upair_not_empty. Qed.

Lemma pair_refl (x: set): pair x x = single (single x).
Proof.
  unfold pair.
  rewrite upair_refl.
  apply upair_refl.
Qed.

Lemma pair_inj (x y z v: set): pair x y = pair z v <-> x = z /\ y = v.
Proof.
  symmetry.
  split.
  intros [].
  now subst z v.
  intros H.
  rewrite <- set_eq_ext in H.
  assert (x = z).
  + specialize (H (single x)).
    apply proj1 in H.
    rewrite !in_pair in H.
    specialize (H (or_introl eq_refl)).
    destruct H.
    apply single_inj, H.
    rewrite <- set_eq_ext in H.
    specialize (H x) as Hx.
    apply proj1 in Hx.
    rewrite in_single, in_upair in Hx.
    specialize (Hx eq_refl).
    destruct Hx as [Hx | Hx].
    exact Hx.
    subst v.
    specialize (H z).
    apply proj2 in H.
    rewrite in_single, in_upair in H.
    specialize (H (or_introl eq_refl)).
    now symmetry.
  + split.
    exact H0.
    subst z.
    specialize (H {x, y}) as Hy.
    rewrite !in_pair in Hy.
    apply proj1 in Hy.
    specialize (Hy (or_intror eq_refl)).
    destruct Hy as [Hy | Hy].
    all: rewrite <- set_eq_ext in Hy.
    - specialize (Hy y).
      rewrite in_upair, in_single in Hy.
      apply proj1 in Hy.
      specialize (Hy (or_intror eq_refl)).
      subst y.
      specialize (H {x, v}).
      apply proj2 in H.
      rewrite !in_pair in H.
      specialize (H (or_intror eq_refl)).
      destruct H.
      rewrite <- set_eq_ext in H.
      specialize (H v).
      rewrite in_upair, in_single in H.
      apply proj1 in H.
      specialize (H (or_intror eq_refl)).
      now symmetry.
      rewrite <- set_eq_ext in H.
      specialize (H v).
      rewrite !in_upair in H.
      apply proj1 in H.
      specialize (H (or_intror eq_refl)).
      now destruct H.
    - specialize (Hy y) as H0.
      rewrite !in_upair in H0.
      apply proj1 in H0.
      specialize (H0 (or_intror eq_refl)).
      destruct H0.
      subst y.
      specialize (Hy v).
      rewrite !in_upair in Hy.
      apply proj2 in Hy.
      specialize (Hy (or_intror eq_refl)).
      now destruct Hy.
      exact H0.
Qed.

Lemma union_pair (x y: set): ∪ pair x y = {x, y}.
Proof.
  apply set_eq_ext.
  intros z.
  rewrite in_union, in_upair.
  setoid_rewrite in_pair.
  split.
  + intros [p [[Hp | Hp] Hz]].
    all: subst p.
    left.
    apply in_single, Hz.
    apply in_upair, Hz.
  + intros [H | H].
    all: subst z.
    all: exists {x, y}.
    all: split.
    1, 3: now right.
    all: apply in_upair.
    now left.
    now right.
Qed.

Lemma intersect_pair (x y: set): ∩ pair x y = single x.
Proof.
  apply set_eq_ext.
  intros z.
  rewrite in_intersect, in_single.
  2: apply pair_not_empty.
  setoid_rewrite in_pair.
  split.
  + intros H.
    specialize (H (single x) (or_introl eq_refl)).
    apply in_single, H.
  + intros H p [Hp | Hp].
    all: subst z p.
    now apply in_single.
    apply in_upair.
    now left.
Qed.

Definition cartisian (X Y: set): set :=
  ∪ { { pair x y | y ⋴ Y } | x ⋴ X }.

Lemma in_cartisian (z X Y: set): z ∈ cartisian X Y <-> exists x y, x ∈ X /\ y ∈ Y /\ z = pair x y.
Proof.
  unfold cartisian.
  rewrite in_flat_map.
  setoid_rewrite in_map.
  split.
  + intros [x [Hx [y [Hy H]]]].
    now exists x, y.
  + intros [x [y [Hx [Hy H]]]].
    exists x.
    split.
    exact Hx.
    now exists y.
Qed.

Lemma cartisian_inj (X Y Z V: set): X <> Ø -> Y <> Ø -> cartisian X Y = cartisian Z V <-> X = Z /\ Y = V.
Proof.
  intros HX HY.
  assert (exists x, x ∈ X).
    destruct (dec (forall x, x ∉ X)).
    destruct HX.
    apply antisymmetry.
    1, 2: intros z Hz.
    now destruct (n z).
    now apply in_empty in Hz.
    destruct (dec (exists x, x ∈ X)).
    assumption.
    destruct n.
    intros z Hz.
    destruct n0.
    now exists z.
  assert (exists y, y ∈ Y).
    destruct (dec (forall y, y ∉ Y)).
    destruct HY.
    apply antisymmetry.
    1, 2: intros z Hz.
    now destruct (n z).
    now apply in_empty in Hz.
    destruct (dec (exists y, y ∈ Y)).
    assumption.
    destruct n.
    intros z Hz.
    destruct n0.
    now exists z.
  clear HX HY.
  destruct H as [x HX].
  destruct H0 as [y HY].
  symmetry.
  split.
  intros [].
  now subst Z V.
  intros H.
  rewrite <- set_eq_ext in H.
  assert (x ∈ Z /\ y ∈ V).
    specialize (H (pair x y)).
    rewrite !in_cartisian in H.
    apply proj1 in H.
    destruct H as [x' [y' [HZ [HV H]]]].
    now exists x, y.
    apply pair_inj in H.
    destruct H.
    now subst y' x'.
  destruct H0 as [HZ HV].
  split.
  + apply set_eq_ext.
    intros z.
    specialize (H (pair z y)).
    rewrite !in_cartisian in H.
    split.
    2: symmetry in H.
    all: apply proj1 in H.
    all: intros Hz.
    all: destruct H as [z' [y' [Hz' [_ H]]]].
    1, 3: now exists z, y.
    all: apply pair_inj in H.
    all: destruct H as [H _].
    all: now subst z'.
  + apply set_eq_ext.
    intros z.
    specialize (H (pair x z)).
    rewrite !in_cartisian in H.
    split.
    2: symmetry in H.
    all: apply proj1 in H.
    all: intros Hz.
    all: destruct H as [x' [z' [_ [Hz' H]]]].
    1, 3: now exists x, z.
    all: apply pair_inj in H.
    all: destruct H as [_ H].
    all: now subst z'.
Qed.
