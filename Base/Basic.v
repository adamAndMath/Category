Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.PropExtensionality.
Require Export Coq.Logic.Classical.
Require Export Coq.Logic.Epsilon.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Program.Basics.
Require Export Coq.Program.Tactics.
Global Set Universe Polymorphism.
Global Set Polymorphic Inductive Cumulativity.

Lemma dec (P: Prop): {P} + {~P}.
Proof.
  enough (inhabited ({P} + {~P})).
  destruct (epsilon H (fun _ => True)).
  now left.
  now right.
  destruct (classic P).
  all: constructor.
  now left.
  now right.
Qed.

Lemma eq_sig {T} {P: T -> Prop} (x y: sig P): x = y <-> proj1_sig x = proj1_sig y.
Proof.
  split; intros H.
  now f_equal.
  apply eq_sig_hprop.
  intro.
  apply proof_irrelevance.
  exact H.
Qed.

Instance forall_iff T: Proper (pointwise_relation T iff ==> iff) (fun P => forall x, P x).
Proof.
  intros P Q H.
  split.
  all: intros HP x.
  all: now apply H.
Qed.

Instance unique_iff T: Proper (pointwise_relation T iff ==> pointwise_relation T iff) (@unique T).
Proof.
  intros P Q H x.
  unfold unique.
  f_equiv.
  apply H.
  apply forall_iff.
  intros y.
  change (?P -> ?Q) with (impl P Q).
  now f_equiv.
Qed.

Lemma ex_forall {T} {F: T -> Type} (P: forall x, F x -> Prop): (forall x, exists y, P x y) -> exists (f: forall x, F x), forall x, P x (f x).
Proof.
  intros H.
  assert (forall x, inhabited (F x)) as i.
    intros x.
    now destruct (H x).
  exists (fun x => epsilon (i x) (P x)).
  intros x.
  apply epsilon_spec, H.
Qed.

Lemma inhabit_forall {T} (F: T -> Type): (forall x, inhabited (F x)) -> inhabited (forall x, F x).
Proof.
  intros H.
  constructor.
  intros x.
  exact (epsilon (H x) (fun _ => True)).
Qed.

Lemma iff_and_l P Q1 Q2: (P /\ Q1 <-> P /\ Q2) <-> (P -> Q1 <-> Q2).
Proof.
  split.
  + intros H p.
    split.
    all: intros q.
    all: now apply H.
  + intros H.
    split.
    all: intros [p q].
    all: split.
    1, 3: exact p.
    all: now apply H.
Qed.

Lemma iff_and_r P Q1 Q2: (Q1 /\ P <-> Q2 /\ P) <-> (P -> Q1 <-> Q2).
Proof.
  rewrite !(and_comm _ P).
  apply iff_and_l.
Qed.

Lemma List_NoDup_app {A} (l1 l2: list A): List.NoDup (l1 ++ l2) <-> List.NoDup l1 /\ List.NoDup l2 /\ forall x, List.In x l1 -> ~List.In x l2.
Proof.
  induction l1; simpl.
  split.
  intros H.
  repeat split.
  constructor.
  exact H.
  easy.
  easy.
  split.
  intros H.
  inversion_clear H.
  apply IHl1 in H1.
  destruct H1 as [? []].
  repeat split.
  constructor.
  contradict H0.
  apply List.in_app_iff.
  now left.
  exact H.
  exact H1.
  intros x Hx.
  destruct Hx.
  subst a.
  contradict H0.
  apply List.in_app_iff.
  now right.
  now apply H2.
  intros [H0 [H2 H3]].
  inversion_clear H0.
  constructor.
  intros H4.
  apply List.in_app_iff in H4.
  destruct H4.
  contradiction.
  apply (H3 a).
  now left.
  exact H0.
  apply IHl1.
  repeat split.
  1, 2: assumption.
  intros x Hx.
  apply H3.
  now right.
Qed.

Lemma List_NoDup_map {A B} (f: A -> B) (l: list A): List.NoDup l /\ (forall x y, List.In x l -> List.In y l -> f x = f y -> x = y) <-> List.NoDup (List.map f l).
Proof.
  split.
  1: intros [Hl Hf].
  2: intros H.
  all: induction l; simpl.
  constructor.
  2: split.
  2: constructor.
  2: easy.
  + constructor.
    intros H.
    apply List.in_map_iff in H.
    destruct H as [x [e Hx]].
    apply Hf in e.
    subst x.
    now inversion_clear Hl.
    1, 2: now [> right | left].
    apply IHl.
    now inversion_clear Hl.
    intros x y Hx Hy.
    apply Hf.
    all: now right.
  + simpl in H.
    inversion_clear H.
    specialize (IHl H1).
    destruct IHl.
    split.
    constructor.
    contradict H0.
    now apply List.in_map.
    exact H.
    intros x y Hx Hy.
    destruct Hx, Hy.
    now subst x y.
    1: subst x.
    2: subst y.
    1, 2: intros e.
    1, 2: destruct H0.
    1: rewrite e.
    2: rewrite <- e.
    1, 2: now apply List.in_map.
    now apply H2.
Qed.

Lemma List_NoDup_flat_map {A B} (f: A -> list B) (l: list A): List.NoDup (List.filter (fun x => if dec (nil = f x) then false else true) l) /\ (forall xs, List.In xs l -> List.NoDup (f xs)) /\ (forall xs ys x, List.In xs l -> List.In ys l -> List.In x (f xs) -> List.In x (f ys) -> xs = ys) <-> List.NoDup (List.flat_map f l).
Proof.
  split.
  1: intros [Hl [Hls Hf]].
  2: intros H.
  all: induction l; simpl in *.
  constructor.
  2: split.
  2: constructor.
  2: easy.
  + apply List_NoDup_app.
    repeat split.
    apply Hls.
    now left.
    apply IHl.
    destruct (dec (nil = f a)).
    exact Hl.
    now inversion_clear Hl.
    intros xs Hxs.
    apply Hls.
    now right.
    intros xs ys x Hxs Hys.
    apply Hf.
    1, 2: now right.
    intros x Hx Hxs.
    apply List.in_flat_map in Hxs.
    destruct Hxs as [xs [Hxs Hx']].
    absurd (a = xs).
    intros e.
    subst xs.
    destruct (dec (nil = f a)).
    now rewrite <- e in Hx.
    inversion_clear Hl.
    contradict H.
    apply List.filter_In.
    split.
    exact Hxs.
    now destruct (dec (nil = f a)).
    apply Hf with x.
    all: now [> left | right |..].
  + apply List_NoDup_app in H.
    destruct H as [Hfa [Hfl Hla]].
    specialize (IHl Hfl).
    destruct IHl as [Hl [Hls Hf]].
    repeat split.
    destruct (dec (nil = f a)).
    exact Hl.
    constructor.
    intros Ha.
    apply List.filter_In in Ha.
    destruct Ha as [Ha _].
    assert (exists x, List.In x (f a)).
    destruct (f a).
    contradiction.
    exists b.
    now left.
    destruct H as [x Hx].
    apply (Hla x).
    exact Hx.
    apply List.in_flat_map.
    now exists a.
    exact Hl.
    intros xs Hxs.
    destruct Hxs.
    now subst xs.
    now apply Hls.
    intros xs ys x Hxs Hys.
    destruct Hxs, Hys.
    now subst xs ys.
    1: subst xs.
    2: subst ys.
    1, 2: intros Hx Hy.
    1, 2: destruct (Hla x).
    1, 3: assumption.
    1, 2: apply List.in_flat_map.
    now exists ys.
    now exists xs.
    now apply Hf.
Qed.
