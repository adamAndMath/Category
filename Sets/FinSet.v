Require Export Base.

Inductive Tree :=
  | node: list Tree -> Tree.

Definition of_tree (x: Tree): list Tree :=
  match x with
  | node l => l
  end.

Definition tree_rect (P: Tree -> Type) (tnil: P (node nil)) (tcons: forall (hd: Tree) (tl: list Tree) (c: P (node tl)), P (node (hd :: tl)%list)) (x: Tree): P x :=
  let rect := fix rect (l: list Tree): P (node l) :=
    match l with
    | nil => tnil
    | cons x tl => tcons x tl (rect tl)
    end
  in
  match x with
  | node l => rect l
  end.

Definition tree_ind (P: Tree -> Prop) (tnil: P (node nil)) (tcons: forall (hd: Tree) (tl: list Tree) (c: P (node tl)), P (node (hd :: tl)%list)) (x: Tree): P x :=
  let rect := fix rect (l: list Tree): P (node l) :=
    match l with
    | nil => tnil
    | cons x tl => tcons x tl (rect tl)
    end
  in
  match x with
  | node l => rect l
  end.

Fixpoint tree_ind_in (P: Tree -> Prop) (IH: forall l, (forall x, List.In x l -> P x) -> P (node l)) (x: Tree) {struct x}: P x :=
  let rect := fix rect (l: list Tree): forall x, List.In x l -> P x :=
    match l return forall x, List.In x l -> P x with
    | nil => fun _ => False_ind _
    | cons x tl => fun e (H: x = e \/ List.In e tl) =>
      match H with
      | or_introl H => match H in _ = y return P y with eq_refl => tree_ind_in P IH x end
      | or_intror H => rect tl e H
      end
    end
  in
  match x with
  | node l => IH l (rect l)
  end.

Inductive tree_eq: Tree -> Tree -> Prop :=
| tree_eq_intro xs ys:
    (forall x, List.In x xs -> exists y, List.In y ys /\ tree_eq x y) ->
    (forall y, List.In y ys -> exists x, List.In x xs /\ tree_eq x y) ->
    tree_eq (node xs) (node ys).

Lemma tree_eq_elm (xs ys: Tree):
  tree_eq xs ys ->
  (forall x, List.In x (of_tree xs) -> exists y, List.In y (of_tree ys) /\ tree_eq x y) /\
  (forall y, List.In y (of_tree ys) -> exists x, List.In x (of_tree xs) /\ tree_eq x y).
Proof.
  destruct xs as [xs], ys as [ys].
  simpl.
  intros H.
  now inversion_clear H.
Qed.

Instance tree_equiv: Equivalence tree_eq.
Proof.
  split.
  + intros x.
    induction x using tree_ind_in.
    constructor.
    all: intros x Hx.
    all: exists x; split.
    1, 3: exact Hx.
    all: apply H, Hx.
  + intros x.
    induction x as [xs IH] using tree_ind_in.
    intros [ys] H.
    apply tree_eq_elm in H.
    destruct H as [H1 H2].
    constructor.
    1: intros x Hx.
    2: intros y Hy.
    1: specialize (H2 x Hx).
    2: specialize (H1 y Hy).
    1: destruct H2 as [y [Hy H]].
    2: destruct H1 as [x [Hx H]].
    1: exists y.
    2: exists x.
    all: split.
    1, 3: assumption.
    all: now apply IH.
  + intros x.
    induction x as [xs IH] using tree_ind_in.
    intros [ys] [zs] H1 H2.
    apply tree_eq_elm in H1.
    apply tree_eq_elm in H2.
    destruct H1 as [xy yx], H2 as [yz zy].
    constructor.
    1: clear yx zy.
    2: clear xy yz.
    1: intros x Hx.
    2: intros z Hz.
    1: specialize (xy x Hx).
    2: specialize (zy z Hz).
    1: destruct xy as [y [Hy xy]].
    2: destruct zy as [y [Hy yz]].
    1: specialize (yz y Hy).
    2: specialize (yx y Hy).
    1: destruct yz as [z [Hz yz]].
    2: destruct yx as [x [Hx xy]].
    1: exists z.
    2: exists x.
    all: split.
    1, 3: assumption.
    all: now apply (IH x Hx y).
Qed.

Definition tree_in (x xs: Tree): Prop :=
  exists y, List.In y (of_tree xs) /\ tree_eq y x.

Lemma tree_eq_iff (x y: Tree): tree_eq x y <-> forall e, tree_in e x <-> tree_in e y.
Proof.
  split.
  + intros H e.
    apply tree_eq_elm in H.
    destruct H as [Hx Hy].
    split.
    all: intros [e1 [H1 H]].
    1: specialize (Hx e1 H1).
    2: specialize (Hy e1 H1).
    1: destruct Hx as [e2 [H2 H3]].
    2: destruct Hy as [e2 [H2 H3]].
    all: exists e2; split.
    1, 3: exact H2.
    all: now transitivity e1.
  + intros H.
    destruct x as [xs], y as [ys].
    constructor.
    all: intros e He.
    all: specialize (H e).
    all: [> apply proj1 in H | apply proj2 in H].
    all: destruct H as [e1 [H1 H]].
    1, 3: now exists e.
    all: now exists e1.
Qed.

Instance tree_in_morph: Proper (tree_eq ==> tree_eq ==> iff) tree_in.
Proof.
  enough (Proper (tree_eq ==> tree_eq ==> impl) tree_in).
  now split; apply H.
  intros x y H1 X Y H2 [e [He H]].
  apply tree_eq_elm, proj1 in H2.
  specialize (H2 e He).
  destruct H2 as [e1 [He1 H2]].
  exists e1.
  split.
  exact He1.
  now rewrite <- H2, H.
Qed.

Definition sub_tree (x y: Tree) := forall e, tree_in e x -> tree_in e y.

Instance sub_tree_preorder: PreOrder sub_tree.
Proof.
  split.
  + intros x y H.
    exact H.
  + intros x y z xy yz e H.
    apply yz, xy, H.
Qed.

Instance sub_tree_partialorder: PartialOrder tree_eq sub_tree.
Proof.
  intros x y.
  simpl.
  rewrite tree_eq_iff.
  split.
  + intros H.
    split.
    all: intros e.
    all: apply H.
  + intros [H1 H2] e.
    split.
    apply H1.
    apply H2.
Qed.

Lemma tin_ind (P: Tree -> Prop):
  Proper (tree_eq ==> iff) P ->
  (forall X, (forall x, tree_in x X -> P x) -> P X) ->
  forall X, P X.
Proof.
  intros HP IH X.
  induction X using tree_ind_in.
  apply IH.
  intros x [e [He H1]].
  rewrite <- H1.
  apply H, He.
Qed.

Definition ɛ_tree: (Tree -> Prop) -> Tree :=
  epsilon (inhabits (node nil)).

Lemma ɛ_tree_correct (P: Tree -> Prop): (exists x, P x) -> P (ɛ_tree P).
Proof. apply epsilon_spec. Qed.

Instance ɛ_tree_ext: Proper (pointwise_relation _ iff ==> eq) ɛ_tree.
Proof.
  intros P Q H.
  f_equal.
  extensionality x.
  apply propositional_extensionality, H.
Qed.

Definition Nf (X: Tree): Tree := ɛ_tree (tree_eq X).

Lemma tree_eq_Nf (X: Tree): tree_eq X (Nf X).
Proof.
  unfold Nf.
  apply ɛ_tree_correct.
  now exists X.
Qed.

Lemma Nf_idem (X: Tree): Nf (Nf X) = Nf X.
Proof.
  apply ɛ_tree_ext.
  intros Y.
  split; intro H.
  all: rewrite <- H.
  2: symmetry.
  all: apply tree_eq_Nf.
Qed.

Lemma tree_Nf_eq (X Y: Tree): tree_eq X Y <-> Nf X = Nf Y.
Proof.
  split.
  + intros H.
    apply ɛ_tree_ext.
    intro x.
    now rewrite H.
  + intros H.
    rewrite tree_eq_Nf, H.
    symmetry.
    apply tree_eq_Nf.
Qed.

Structure fset: Type := tree_fset {
  fset_tree: {X | Nf X = X};
}.

Declare Scope fset_scope.
Delimit Scope fset_scope with fset.
Bind Scope fset_scope with fset.
Local Open Scope fset_scope.

Definition NSf (X: Tree): fset := tree_fset (exist _ (Nf X) (Nf_idem X)).

Lemma tree_eq_NSf (X: Tree): tree_eq X (proj1_sig (fset_tree (NSf X))).
Proof. apply tree_eq_Nf. Qed.

Definition fIn (X Y: fset): Prop := tree_in (proj1_sig (fset_tree X)) (proj1_sig (fset_tree Y)).

Infix "∈" := fIn (at level 70): fset_scope.
Notation "x ∉ X" := (~fIn x X) (at level 70): fset_scope.

Lemma tree_in_fset (X Y: fset): tree_in (proj1_sig (fset_tree X)) (proj1_sig (fset_tree Y)) -> X ∈ Y.
Proof. intro H. exact H. Qed.

Lemma tree_in_NSf (X Y: Tree): tree_in X Y -> NSf X ∈ NSf Y.
Proof.
  intro H.
  apply tree_in_fset.
  simpl.
  rewrite <- !tree_eq_Nf.
  exact H.
Qed.

Definition subfset (X Y: fset): Prop :=
  forall z, z ∈ X -> z ∈ Y.

Infix "⊆" := subfset (at level 70): fset_scope.

Instance subfset_preorder: PreOrder subfset.
Proof.
  constructor.
  easy.
  intros X Y Z XY YZ x H.
  apply YZ, XY, H.
Qed.

Theorem subfset_subtree (X Y: fset): sub_tree (proj1_sig (fset_tree X)) (proj1_sig (fset_tree Y)) -> X ⊆ Y.
Proof.
  intros XY z zX.
  apply XY, zX.
Qed.

Instance subfset_partialorder: PartialOrder eq subfset.
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
  apply tree_Nf_eq.
  apply antisymmetry.
  1: clear YX.
  2: clear XY; rename YX into XY.
  all: intros a H.
  all: rewrite tree_eq_Nf in H |- *.
  all: exact (XY (NSf a) H).
Qed.

Theorem fset_eq_ext (X Y: fset): (forall z, z ∈ X <-> z ∈ Y) <-> X = Y.
Proof.
  split.
  intros H.
  apply antisymmetry.
  1, 2: intro z.
  1, 2: apply H.
  intros H z.
  now subst Y.
Qed.

Theorem fset_tree_eq (X Y: fset): tree_eq (proj1_sig (fset_tree X)) (proj1_sig (fset_tree Y)) -> X = Y.
Proof.
  intros H.
  apply partial_order_equivalence in H.
  destruct H as [XY YX].
  apply antisymmetry.
  all: now apply subfset_subtree.
Qed.

Definition indexf (X: fset): list fset :=
  match proj1_sig (fset_tree X) with
  | node l => List.map NSf l
  end.

Definition fset_of (l: list fset): fset :=
  tree_fset (exist _ (Nf (node (List.map (fun x => proj1_sig (fset_tree x)) l))) (Nf_idem _)).

Lemma fset_of_indexf (X: fset): fset_of (indexf X) = X.
Proof.
  apply fset_tree_eq.
  unfold indexf; simpl.
  generalize (proj1_sig (fset_tree X)).
  clear X; intros [X].
  simpl.
  rewrite <- tree_eq_Nf.
  rewrite tree_eq_iff.
  intros e.
  split.
  all: intros [a [Ha H]].
  all: simpl in Ha.
  apply List.in_map_iff in Ha.
  destruct Ha as [a' [Ha Ha']].
  subst a.
  apply List.in_map_iff in Ha'.
  destruct Ha' as [a [Ha' Ha]].
  subst a'.
  simpl in H.
  rewrite <- tree_eq_Nf in H.
  now exists a.
  exists (Nf a).
  simpl.
  split.
  apply List.in_map_iff.
  exists (NSf a).
  simpl.
  repeat split.
  apply List.in_map, Ha.
  rewrite <- tree_eq_Nf.
  exact H.
Qed.

Theorem in_fset_of x xs: x ∈ fset_of xs <-> List.In x xs.
Proof.
  unfold fIn.
  simpl.
  rewrite <- tree_eq_Nf.
  split.
  + intros [a [Ha H]].
    simpl in Ha.
    apply List.in_map_iff in Ha.
    destruct Ha as [e [Ha He]].
    subst a.
    apply fset_tree_eq in H.
    now subst e.
  + intros H.
    exists (proj1_sig (fset_tree x)).
    simpl.
    split.
    now apply (List.in_map (fun x => proj1_sig (fset_tree x))).
    reflexivity.
Qed.

Theorem in_indexf (x X: fset): x ∈ X <-> List.In x (indexf X).
Proof.
  rewrite <- (fset_of_indexf X) at 1.
  apply in_fset_of.
Qed.

Lemma fset_NSf (X: fset): exists x: Tree, X = NSf x.
Proof.
  destruct X as [[X H]].
  exists X.
  apply fset_tree_eq, tree_eq_Nf.
Qed.

Lemma fset_ind (P: fset -> Prop):
  (forall X, (forall x, x ∈ X -> P x) -> P X) ->
  forall X, P X.
Proof.
  intros IH X.
  destruct (fset_NSf X) as [x H].
  subst X.
  revert x.
  apply tin_ind.
  intros X Y XY.
  f_equiv.
  apply fset_tree_eq.
  simpl.
  rewrite <- !tree_eq_Nf.
  exact XY.
  intros X H.
  apply IH.
  intros Y Hx.
  destruct (fset_NSf Y) as [x H0].
  subst Y.
  apply H.
  rewrite (tree_eq_Nf x).
  rewrite (tree_eq_Nf X).
  exact Hx.
Qed.

Definition empty: fset := fset_of nil.
Notation Ø := empty.

Theorem in_empty (x: fset): x ∉ Ø.
Proof.
  exact (proj1 (in_fset_of x nil)).
Qed.

Theorem not_empty (x: fset): x <> Ø <-> exists z, z ∈ x.
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

Definition single (x: fset): fset :=
  fset_of (x :: nil).

Theorem in_single (z x: fset): z ∈ single x <-> z = x.
Proof.
  unfold single.
  rewrite in_fset_of.
  split.
  now intros [].
  intros H.
  now left.
Qed.

Theorem single_inj (x y: fset): single x = single y <-> x = y.
Proof.
  symmetry.
  split.
  all: intros H.
  now subst y.
  rewrite <- fset_eq_ext in H.
  specialize H with x.
  rewrite !in_single in H.
  now apply H.
Qed.

Theorem single_not_empty (x: fset): single x <> Ø.
Proof.
  apply not_empty.
  exists x.
  now apply in_single.
Qed.

Definition upair (X Y: fset): fset :=
  fset_of (X :: Y :: nil).

Notation "{ x , y }" := (upair x y) (at level 0, x at level 99, y at level 99): fset_scope.

Theorem in_upair (z x y: fset): z ∈ {x, y} <-> z = x \/ z = y.
Proof.
  unfold upair.
  rewrite in_fset_of.
  simpl.
  f_equiv.
  easy.
  split.
  now intros [].
  intros H.
  now left.
Qed.

Lemma upair_not_empty (x y: fset): upair x y <> Ø.
Proof.
  apply not_empty.
  exists x.
  apply in_upair.
  now left.
Qed.

Lemma upair_refl (x: fset): upair x x = single x.
Proof.
  apply fset_eq_ext.
  intros z.
  rewrite in_upair, in_single.
  split.
  now intros [H | H].
  intros H.
  now left.
Qed.

Definition union (X: fset): fset :=
  fset_of (List.flat_map indexf (indexf X)).

Notation "∪ X" := (union X) (at level 40): fset_scope.

Theorem in_union (x X: fset): x ∈ ∪ X <-> exists y, y ∈ X /\ x ∈ y.
Proof.
  unfold union.
  rewrite in_fset_of.
  split.
  + intros H.
    apply List.in_flat_map in H.
    destruct H as [a [Ha Hx]].
    exists a.
    split.
    all: now apply in_indexf.
  + intros [y [yX xy]].
    apply List.in_flat_map.
    exists y.
    split.
    all: now apply in_indexf.
Qed.

Definition union_single (x: fset): ∪ (single x) = x.
Proof.
  apply fset_eq_ext.
  intros z.
  rewrite in_union.
  setoid_rewrite in_single.
  split.
  + intros [y [Hy Hz]].
    now subst y.
  + intros Hz.
    now exists x.
Qed.

Definition map (f: fset -> fset) (X: fset): fset :=
  fset_of (List.map f (indexf X)).

Notation "{ y | x ⋴ X }" := (map (fun x => y) X) (at level 0, y at level 99, x, X at level 89): fset_scope.

Lemma in_map (z: fset) (f: fset -> fset) (X: fset): z ∈ { f x | x ⋴ X } <-> exists x, x ∈ X /\ z = f x.
Proof.
  unfold map.
  rewrite in_fset_of.
  rewrite List.in_map_iff.
  f_equiv.
  intros x.
  rewrite and_comm.
  f_equiv.
  symmetry.
  apply in_indexf.
  easy.
Qed.

Lemma in_map' (z: fset) (f: fset -> fset) (X: fset): z ∈ X -> f z ∈ { f x | x ⋴ X}.
Proof.
  intros Hz.
  apply in_map.
  now exists z.
Qed.

Lemma map_id (X: fset): {x | x ⋴ X} = X.
Proof.
  apply fset_eq_ext.
  intros z.
  rewrite in_map.
  split.
  intros [x [Hx Hz]].
  now subst z.
  intros Hz.
  now exists z.
Qed.

Lemma map_comp (f g: fset -> fset) (X: fset): {f y | y ⋴ {g x | x ⋴ X}} = {f (g x) | x ⋴ X}.
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

Lemma map_single (f: fset -> fset) (x: fset): {f x | x ⋴ single x} = single (f x).
Proof.
  apply fset_eq_ext.
  intros z.
  rewrite in_map.
  setoid_rewrite in_single.
  split.
  + intros [y [Hy Hz]].
    now subst y.
  + intros H.
    now exists x.
Qed.

Lemma in_flat_map (z: fset) (f: fset -> fset) (X: fset): z ∈ ∪ {f x | x ⋴ X} <-> exists y, y ∈ X /\ z ∈ f y.
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

Definition sep (P: fset -> Prop) (X: fset): fset :=
  fset_of (List.filter (fun x => if dec (P x) then true else false) (indexf X)).

Notation "{ x ⋴ X | P }" := (sep (fun x => P) X) (at level 0, x, X at level 99, P at level 99): fset_scope.

Lemma list_in_filter {A} (P: A -> bool) (x: A) (l: list A): List.In x (List.filter P l) <-> P x = true /\ List.In x l.
Proof.
  induction l.
  all: simpl.
  easy.
  split.
  + intros H.
    remember (P a).
    rename Heqb into Ha.
    symmetry in Ha.
    destruct b.
    simpl in H |- *.
    destruct H.
    split.
    now subst a.
    now left.
    all: apply IHl in H.
    all: split.
    1, 3: easy.
    all: now right.
  + intros [Hx [H | H]].
    subst a.
    rewrite Hx.
    now left.
    destruct (P a).
    right.
    all: now apply IHl.
Qed.

Lemma in_sep (z: fset) (P: fset -> Prop) (X: fset): z ∈ { x ⋴ X | P x } <-> z ∈ X /\ P z.
Proof.
  unfold sep.
  rewrite in_fset_of.
  rewrite list_in_filter.
  rewrite and_comm.
  f_equiv.
  symmetry.
  apply in_indexf.
  now destruct (dec (P z)).
Qed.

Definition intersect (X: fset) :=
  { x ⋴ ∪ X | forall y, y ∈ X -> x ∈ y}.

Notation "∩ X" := (intersect X) (at level 40): fset_scope.

Lemma in_intersect (z X: fset): X <> Ø -> z ∈ ∩ X <-> forall x, x ∈ X -> z ∈ x.
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

Lemma intersect_single (x: fset): ∩ single x = x.
Proof.
  apply fset_eq_ext.
  intros z.
  rewrite in_intersect.
  2: apply single_not_empty.
  setoid_rewrite in_single.
  split; intros Hz.
  now apply Hz.
  intros e H.
  now subst e.
Qed.

Definition binunion (x y: fset) := ∪ {x, y}.
Infix "∪" := binunion (at level 50, left associativity): fset_scope.

Lemma in_binunion (z x y: fset): z ∈ x ∪ y <-> z ∈ x \/ z ∈ y.
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

Definition binintersect (X Y: fset) := {x ⋴ X | x ∈ Y}.
Infix "∩" := binintersect (at level 50, left associativity): fset_scope.

Lemma in_binintersect (z x y: fset): z ∈ x ∩ y <-> z ∈ x /\ z ∈ y.
Proof.
  unfold binintersect.
  exact (in_sep _ _ _).
Qed.

Definition diff (X Y: fset) := {x ⋴ X | x ∉ Y}.
Infix "\" := diff (at level 50, left associativity): fset_scope.

Lemma in_diff (z X Y: fset): z ∈ X \ Y <-> z ∈ X /\ z ∉ Y.
Proof.
  unfold diff.
  rewrite in_sep.
  reflexivity.
Qed.

Fixpoint pow_index (l: list fset): list fset :=
  match l with
  | nil => Ø :: nil
  | cons x tl => (pow_index tl ++ List.map (fun s => single x ∪ s) (pow_index tl))%list
  end.

Definition pow (X: fset): fset :=
  fset_of (pow_index (indexf X)).

Lemma in_pow (z X: fset): z ∈ pow X <-> z ⊆ X.
Proof.
  unfold pow, subfset.
  rewrite in_fset_of.
  setoid_rewrite in_indexf at 2.
  generalize (indexf X).
  clear X; intros xs.
  split.
  + induction xs in z |- *; simpl.
    intros [H | []].
    subst z.
    apply in_empty.
    rewrite List.in_app_iff.
    rewrite List.in_map_iff.
    intros [H | [x [Hz H]]] e He.
    right.
    now apply (IHxs z).
    subst z.
    rewrite in_binunion in He.
    rewrite in_single in He.
    destruct He; [left | right].
    now symmetry.
    now apply (IHxs x).
  + intros H.
    induction xs in z, H |- *; simpl.
    left.
    apply fset_eq_ext.
    intros e.
    split.
    1, 2: intros He.
    1, 2: apply False_ind.
    eapply in_empty, He.
    eapply H, He.
    apply List.in_or_app.
    destruct (dec (a ∈ z)).
    all: [> right | left].
    apply List.in_map_iff.
    exists (z \ single a).
    split.
    apply fset_eq_ext.
    intros e.
    rewrite in_binunion, in_diff, in_single.
    split.
    intros [He | [He _]].
    now subst a.
    exact He.
    intros He.
    destruct (dec (e = a)).
    1, 2: now [> left | right].
    all: apply IHxs.
    all: intros e He.
    rewrite in_diff, in_single in He.
    destruct He as [He Hn].
    all: specialize (H e He).
    all: destruct H.
    2, 4: exact H.
    now destruct Hn.
    now subst a.
Qed.

Definition pair (x y: fset): fset :=
  { single x, { x, y } }.

Lemma in_pair (z x y: fset): z ∈ pair x y <-> z = single x \/ z = {x, y}.
Proof. apply in_upair. Qed.

Lemma pair_not_empty (x y: fset): pair x y <> Ø.
Proof. apply upair_not_empty. Qed.

Lemma pair_refl (x: fset): pair x x = single (single x).
Proof.
  unfold pair.
  rewrite upair_refl.
  apply upair_refl.
Qed.

Lemma pair_inj (x y z v: fset): pair x y = pair z v <-> x = z /\ y = v.
Proof.
  symmetry.
  split.
  intros [].
  now subst z v.
  intros H.
  rewrite <- fset_eq_ext in H.
  assert (x = z).
  + specialize (H (single x)).
    apply proj1 in H.
    rewrite !in_pair in H.
    specialize (H (or_introl eq_refl)).
    destruct H.
    apply single_inj, H.
    rewrite <- fset_eq_ext in H.
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
    all: rewrite <- fset_eq_ext in Hy.
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
      rewrite <- fset_eq_ext in H.
      specialize (H v).
      rewrite in_upair, in_single in H.
      apply proj1 in H.
      specialize (H (or_intror eq_refl)).
      now symmetry.
      rewrite <- fset_eq_ext in H.
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

Lemma union_pair (x y: fset): ∪ pair x y = {x, y}.
Proof.
  apply fset_eq_ext.
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

Lemma intersect_pair (x y: fset): ∩ pair x y = single x.
Proof.
  apply fset_eq_ext.
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

Definition cartisian (X Y: fset): fset :=
  ∪ { { pair x y | y ⋴ Y } | x ⋴ X }.

Lemma in_cartisian (z X Y: fset): z ∈ cartisian X Y <-> exists x y, x ∈ X /\ y ∈ Y /\ z = pair x y.
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

Lemma in_cartisian' (x y X Y: fset): pair x y ∈ cartisian X Y <-> x ∈ X /\ y ∈ Y.
Proof.
  rewrite in_cartisian.
  split.
  + intros [x' [y' [Hx [Hy H]]]].
    apply pair_inj in H.
    destruct H.
    now subst x' y'.
  + intros [Hx Hy].
    now exists x, y.
Qed.

Lemma cartisian_inj (X Y Z V: fset): X <> Ø -> Y <> Ø -> cartisian X Y = cartisian Z V <-> X = Z /\ Y = V.
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
  rewrite <- fset_eq_ext in H.
  assert (x ∈ Z /\ y ∈ V).
    specialize (H (pair x y)).
    rewrite !in_cartisian' in H.
    now apply H.
  destruct H0 as [HZ HV].
  split.
  + apply fset_eq_ext.
    intros z.
    specialize (H (pair z y)).
    rewrite !in_cartisian' in H.
    split.
    2: symmetry in H.
    all: apply proj1 in H.
    all: intros Hz.
    all: now apply H.
  + apply fset_eq_ext.
    intros z.
    specialize (H (pair x z)).
    rewrite !in_cartisian' in H.
    split.
    2: symmetry in H.
    all: apply proj1 in H.
    all: intros Hz.
    all: now apply H.
Qed.

Module FinSet.
Section category.
Let obj := fset.

Structure hom (S T: obj) := Hom {
  rel: fset;
  sign: rel ⊆ cartisian S T;
  functional: forall x, x ∈ S -> exists! y, pair x y ∈ rel
}.

Coercion rel: hom >-> fset.

Lemma hom_eq {S T: obj} (f g: hom S T): f = g <-> (forall x y, pair x y ∈ f <-> pair x y ∈ g).
Proof.
  split; intros H.
  now subst g.
  destruct f as [f Hf1 Hf2], g as [g Hg1 Hg2].
  simpl in H.
  enough (f = g).
  subst g.
  f_equiv; apply proof_irrelevance.
  apply fset_eq_ext.
  intros p.
  split.
  all: intros Hp.
  1: specialize (Hf1 p Hp) as e.
  2: specialize (Hg1 p Hp) as e.
  all: apply in_cartisian in e.
  all: destruct e as [x [y [Hx [Hy e]]]].
  all: subst p.
  all: apply H, Hp.
Qed.

Program Definition homFun {X Y: fset} (f: fset -> fset) (Hf: forall x, x ∈ X -> f x ∈ Y): hom X Y := {|
  rel := { pair x (f x) | x ⋴ X };
|}.
Next Obligation.
  intros p Hp.
  apply in_map in Hp.
  destruct Hp as [x [Hx Hp]].
  subst p.
  apply in_cartisian'.
  split.
  exact Hx.
  apply Hf, Hx.
Qed.
Next Obligation.
  exists (f x).
  split.
  apply (in_map' x), H.
  intros y Hy.
  apply in_map in Hy.
  destruct Hy as [x' [_ Hp]].
  apply pair_inj in Hp.
  destruct Hp as [Hx' Hy].
  now subst x'.
Qed.

Lemma Fun_def {X Y: fset} (f: hom X Y) (x: fset): sig (fun y => x ∈ X -> pair x y ∈ f).
Proof.
  exists (epsilon (inhabits x) (fun y => x ∈ X -> pair x y ∈ f)).
  apply epsilon_spec.
  destruct (classic (x ∈ X)).
  apply (functional _ _ f) in H.
  destruct H as [y [H _]].
  now exists y.
  now exists Ø.
Qed.

Definition Fun {X Y: fset} (f: hom X Y) (x: fset): fset := proj1_sig (Fun_def f x).
Definition Fun_spec {X Y: fset} (f: hom X Y) (x: fset): x ∈ X -> pair x (Fun f x) ∈ f := proj2_sig (Fun_def f x).

Lemma Fun_unique {X Y: fset} (f: hom X Y) (x y: fset): pair x y ∈ f -> Fun f x = y.
Proof.
  intros H.
  assert (x ∈ X) as Hx.
  apply sign in H.
  now apply in_cartisian' in H.
  destruct (functional _ _ f x Hx) as [y' [_ Hy]].
  specialize (Hy y H) as e.
  subst y'.
  symmetry.
  apply Hy.
  now apply Fun_spec.
Qed.

Lemma Fun_unique' {X Y: fset} (f: hom X Y) (x y: fset): x ∈ X -> Fun f x = y -> pair x y ∈ f.
Proof.
  intros Hx Hy.
  subst y.
  apply Fun_spec, Hx.
Qed.

Lemma Fun_to {X Y: fset} (f: hom X Y) (x: fset): x ∈ X -> Fun f x ∈ Y.
Proof.
  intros Hx.
  apply (Fun_spec f) in Hx.
  apply sign in Hx.
  now apply in_cartisian' in Hx.
Qed.

Lemma hom_ext {X Y: fset} (f g: hom X Y): f = g <-> forall x, x ∈ X -> Fun f x = Fun g x.
Proof.
  split.
  all: intros H.
  now subst g.
  apply hom_eq.
  intros x.
  split.
  all: intros Hp.
  all: specialize (sign _ _ _ _ Hp) as He.
  all: apply in_cartisian' in He.
  all: destruct He as [Hx Hy].
  all: specialize (H x Hx).
  all: apply Fun_unique in Hp.
  all: rewrite Hp in H; clear Hp.
  all: subst y.
  all: apply Fun_spec, Hx.
Qed.

Lemma Fun_homFun {X Y: fset} (f: fset -> fset) Hf x: x ∈ X -> @Fun X Y (homFun f Hf) x = f x.
Proof.
  intros Hx.
  apply Fun_unique.
  apply (in_map' x), Hx.
Qed.

Lemma homFun_Fun {X Y: fset} (f: hom X Y): homFun (Fun f) (Fun_to f) = f.
Proof.
  apply hom_eq.
  intros x y.
  simpl.
  rewrite in_map.
  split.
  + intros [x' [Hx Hp]].
    apply pair_inj in Hp.
    destruct Hp as [Hx' Hy].
    subst x' y.
    apply Fun_spec, Hx.
  + intros Hp.
    exists x.
    split.
    apply sign in Hp.
    now apply in_cartisian' in Hp.
    f_equal.
    symmetry.
    apply Fun_unique, Hp.
Qed.

Definition id (A: obj): hom A A :=
  homFun (fun x => x) (fun x Hx => Hx).

Definition comp {A B C: obj} (f: hom B C) (g: hom A B): hom A C :=
  homFun (fun x => Fun f (Fun g x)) (fun x Hx => Fun_to f _ (Fun_to g _ Hx)).

Lemma comp_assoc {A B C D: obj} (f: hom C D) (g: hom B C) (h: hom A B): comp f (comp g h) = comp (comp f g) h.
Proof.
  apply hom_ext.
  intros x Hx.
  transitivity (Fun f (Fun g (Fun h x))).
  2: symmetry.
  all: apply Fun_unique.
  all: apply in_map.
  all: exists x; split.
  1, 3: exact Hx.
  all: f_equal.
  f_equal.
  all: symmetry.
  all: apply Fun_unique.
  apply (in_map' x), Hx.
  apply (in_map' (Fun h x)).
  apply Fun_to, Hx.
Qed.

Lemma comp_id_l {S T: obj} (f: hom S T): comp (id T) f = f.
Proof.
  apply hom_ext.
  intros x Hx.
  apply Fun_unique.
  apply in_map.
  exists x; split.
  exact Hx.
  f_equal.
  symmetry.
  apply Fun_unique.
  apply (in_map' (Fun f x) (fun x => pair x x)).
  apply Fun_to, Hx.
Qed.

Lemma comp_id_r {S T: obj} (f: hom S T): comp f (id S) = f.
Proof.
  apply hom_ext.
  intros x Hx.
  apply Fun_unique.
  apply in_map.
  exists x; split.
  exact Hx.
  do 2 f_equal.
  symmetry.
  apply Fun_unique.
  apply (in_map' x (fun x => pair x x)).
  exact Hx.
Qed.

Definition cat_mixin: Category.mixin_of obj :=
  Category.Mixin obj hom id (@comp) (@comp_assoc) (@comp_id_l) (@comp_id_r).

Canonical cat := Category.Pack obj cat_mixin.

Lemma Fun_id {X: cat} (x: fset): x ∈ X -> Fun (Categories.id X) x = x.
Proof.
  intros Hx.
  apply Fun_unique.
  apply (in_map' x (fun x => pair x x)).
  exact Hx.
Qed.

Lemma Fun_comp {X Y Z: cat} (f: Y ~> Z) (g: X ~> Y) (x: fset): x ∈ X -> Fun (f ∘ g) x = Fun f (Fun g x).
Proof.
  intros Hx.
  apply Fun_unique.
  apply (in_map' x), Hx.
Qed.

End category.

End FinSet.

Coercion FinSet.rel: FinSet.hom >-> fset.
Coercion FinSet.Fun: FinSet.hom >-> Funclass.
Canonical FinSet.cat.
Notation FinSet := FinSet.cat.
