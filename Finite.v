Require Export Instances.
Require Export Instances.Typ.

Definition tfin T :=
  exists l: list T, forall x: T, List.In x l.

Lemma not_tfin T: ~tfin T <-> forall l: list T, exists x: T, ~List.In x l.
Proof.
  split.
  + intros H l.
    assert (~forall x: T, List.In x l).
      contradict H.
      now exists l.
    clear H.
    destruct (classic (exists x: T, ~List.In x l)).
    assumption.
    destruct H0.
    intros x.
    destruct (classic (List.In x l)).
    assumption.
    destruct H.
    now exists x.
  + intros H [l Hl].
    specialize (H l).
    destruct H as [x []].
    apply Hl.
Qed.

Lemma tfin_epic A B (f: A ~> B): epic f -> tfin A -> tfin B.
Proof.
  intros Hf [l Hl].
  rewrite Typ_epic in Hf.
  exists (List.map f l).
  intros y.
  specialize (Hf y).
  destruct Hf as [x Hf].
  subst y.
  apply List.in_map, Hl.
Qed.

Definition fin (C: Category) :=
  tfin C /\ forall x y: C, tfin (x ~> y).

Lemma fin_splitepic {S T: Category} (F: S ~> T): splitepic F -> fin S -> fin T.
Proof.
  intros HF H.
  split; [apply proj1 in H | apply proj2 in H].
  eapply tfin_epic, H.
  apply splitepic_is_epic.
  apply fobj_splitepic, HF.
  intros x y.
  destruct HF as [G HF].
  assert ((x ~> y) = ((F ∘ G) x ~> (F ∘ G) y)).
  now rewrite HF.
  rewrite H0; clear H0.
  specialize (H (G x) (G y)).
  destruct H as [l Hl].
  exists (List.map (fmap F) l).
  intros f'.
  assert (exists f: x ~> y, fmap (F ∘ G) f = f').
  revert f'.
  rewrite HF.
  intros f.
  now exists f.
  destruct H as [f Hf].
  subst f'.
  simpl.
  apply List.in_map, Hl.
Qed.

Lemma fin_splitmonic {S T: Category} (F: S ~> T): splitmonic F -> fin T -> fin S.
Proof.
  intros [G H].
  apply (fin_splitepic G).
  now exists F.
Qed.

Instance fin_iso: Proper (isomorphic Cat ==> iff) fin.
Proof.
  enough (Proper (isomorphic Cat ==> impl) fin).
  now split; apply H.
  intros A B [I].
  red.
  apply (fin_splitepic I).
  apply iso_is_splitepic.
Qed.

Lemma fin_0: fin 0.
Proof.
  split.
  now exists nil.
  easy.
Qed.

Lemma fin_1: fin 1.
Proof.
  split.
  2: intros [] [].
  all: exists (tt :: nil)%list.
  all: intros [].
  all: now left.
Qed.

Lemma fin_coprod (A B: Category): fin A -> fin B -> fin (A + B).
Proof.
  intros Ha Hb.
  split.
  all: [> apply proj1 in Ha | apply proj2 in Ha].
  all: [> apply proj1 in Hb | apply proj2 in Hb].
  + destruct Ha as [xs Hx], Hb as [ys Hy].
    exists (List.map inl xs ++ List.map inr ys)%list.
    intros [x | y].
    all: apply List.in_or_app.
    all: [> left | right].
    all: apply List.in_map.
    apply Hx.
    apply Hy.
  + intros [x | x] [y | y].
    1: apply Ha.
    3: apply Hb.
    all: now exists nil.
Qed.

Lemma fin_prod (A B: Category): fin A -> fin B -> fin (A × B).
Proof.
  intros Ha Hb.
  split.
  all: [> apply proj1 in Ha | apply proj2 in Ha].
  all: [> apply proj1 in Hb | apply proj2 in Hb].
  + destruct Ha as [xs Hx], Hb as [ys Hy].
    exists (List.flat_map (fun x => List.map (fun y => (x, y)) ys) xs).
    intros [x y].
    apply List.in_flat_map.
    exists x.
    split.
    apply Hx.
    apply List.in_map.
    apply Hy.
  + intros [x1 y1] [x2 y2].
    specialize (Ha x1 x2).
    specialize (Hb y1 y2).
    destruct Ha as [fs Hf], Hb as [gs Hg].
    exists (List.flat_map (fun f => List.map (fun g => (f, g)) gs) fs).
    intros [f g].
    apply List.in_flat_map.
    exists f.
    split.
    apply Hf.
    apply List.in_map.
    apply Hg.
Qed.
