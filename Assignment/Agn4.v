Require Export Categories.Poset.
Require Export Instances.
Require Export Congruence.
Require Export Instances.Dual.
Require Export Categories.Typ.

Lemma ex1 (C: Category): is_proset C -> exists D, is_poset D /\ C ≈ D.
Proof.
  intros H.
  assert (exists T (R: T -> T -> Prop) (po: PreOrder R), Proset R ≃ C).
    exists C, connected, _.
    apply proset_ex, H.
  destruct H0 as [T [R [HR HC]]].
  clear H.
  apply iso_cequiv in HC.
  setoid_rewrite <- HC.
  clear C HC.
  set (E x y := R x y /\ R y x).
  assert (Equivalence E) as HE.
    unfold E.
    split; red; intros; split.
    1, 2: reflexivity.
    1, 2: apply H.
    1, 2: now transitivity y.
  set (Rq (x y: Quotient E) := R (elm x) (elm y)).
  assert (PreOrder Rq) as HRq.
    unfold Rq.
    split; red; intros.
    reflexivity.
    now transitivity (elm y).
  assert (PartialOrder eq Rq).
    unfold Rq.
    intros x y.
    split.
    intros H.
    now subst y.
    intros [H1 H2].
    now apply (Quotient_eq E).
  exists (Poset Rq).
  split.
  apply Poset_correct.
  symmetry.
  red.
  unshelve eexists.
  unshelve eexists.
  exact elm.
  exact (fun x y f => f).
  3: apply is_equiv_alt.
  3: split.
  3, 4: red.
  all: simpl.
  all: intros.
  1, 2: apply Proset.hom_eq.
  now exists f.
  exists (quotient E y).
  constructor.
  1: unshelve eexists.
  2: unshelve eexists.
  3, 4: apply Proset.hom_eq.
  all: red; simpl.
  all: apply (repr_correct E y).
Qed.

Lemma ex3_1 {C: CCC} {X Y: C} (g: X ~> Y) (B: C): exists! g': X^B ~> Y^B, forall A (f: A × B ~> X), g' ∘ transpose f = transpose (g ∘ f).
Proof.
  exists (transpose (g ∘ eval X B)).
  split.
  + intros A f.
    apply transpose_inv_inj.
    rewrite transpose_inv_l.
    unfold transpose_inv.
    setoid_rewrite <- (comp_id_l (id B)).
    setoid_rewrite <- fprod_comp.
    rewrite comp_assoc.
    rewrite eval_transpose.
    rewrite <- comp_assoc.
    rewrite eval_transpose.
    reflexivity.
  + intros f H.
    rewrite <- H, <- comp_id_r.
    f_equal.
    rewrite <- (comp_id_r (eval X B)).
    rewrite <- fprod_id.
    apply transpose_inv_r.
Qed.

Lemma ex3_2 {ℂ: CCC} {A' A B C: ℂ} (f: A × B ~> C) (h: A' ~> A): transpose f ∘ h = transpose (f ∘ (h (×) id B)).
Proof.
  apply transpose_inv_inj.
  rewrite transpose_inv_l.
  unfold transpose_inv.
  setoid_rewrite <- (comp_id_l (id B)) at 1.
  setoid_rewrite <- fprod_comp.
  rewrite comp_assoc.
  f_equal.
  apply eval_transpose.
Qed.

Section ex4.
Context {ℂ: CCC} {B: ℂ}.

Program Definition L: co ℂ × ℂ ~> Typ := {|
  fobj p := fst p × B ~> snd p;
  fmap p q f g := snd f ∘ g ∘ (fst f (×) id B);
|}.
Next Obligation.
  rename o into A, o0 into C.
  simpl.
  extensionality g.
  setoid_rewrite fprod_id.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.
Next Obligation.
  rename o3 into A1, o4 into C1, o1 into A2, o2 into C2, o into A3, o0 into C3.
  destruct f as [f1 f2].
  destruct g as [g1 g2].
  simpl in *.
  red in f1, g1; simpl in f1, g1.
  change (Category.hom _ _ ?x ?y) with (x ~> y) in f1, g1.
  symmetry.
  extensionality h.
  unfold comp at 1; simpl; unfold Typ.comp.
  rewrite !comp_assoc, <- comp_assoc.
  f_equal.
  rewrite fprod_comp.
  f_equal.
  apply comp_id_l.
Qed.

Program Definition R: co ℂ × ℂ ~> Typ := {|
  fobj p := @hom ℂ (fst p) (snd p ^ B);
  fmap p q f g := transpose (snd f ∘ (transpose_inv g)) ∘ fst f (*snd f ∘ g ∘ (fst f (×) id B)*);
|}.
Next Obligation.
  rename o into A, o0 into C.
  simpl.
  extensionality g.
  rewrite comp_id_l, transpose_inv_r.
  apply (comp_id_r g).
Qed.
Next Obligation.
  rename o3 into A1, o4 into C1, o1 into A2, o2 into C2, o into A3, o0 into C3.
  destruct f as [f1 f2].
  destruct g as [g1 g2].
  simpl in *.
  red in f1, g1; simpl in f1, g1.
  change (Category.hom _ _ ?x ?y) with (x ~> y) in f1, g1.
  unfold comp; simpl; repeat change (Category.comp _ _ ?f ?g) with (f ∘ g).
  unfold Typ.comp.
  symmetry.
  extensionality h.
  rewrite comp_assoc.
  f_equal.
  apply transpose_inv_inj.
  rewrite transpose_inv_l.
  unfold transpose_inv at 1 3.
  setoid_rewrite <- (comp_id_l (id B)).
  setoid_rewrite <- fprod_comp.
  rewrite !(comp_assoc (eval _ _)).
  rewrite !eval_transpose.
  now rewrite !comp_assoc.
Qed.

Program Definition transpose_to: L ~> R := {|
  transform p f := transpose f;
|}.
Next Obligation.
  rename o1 into A, o2 into C, o into A', o0 into C'.
  destruct f as [f g].
  simpl in *.
  change (A' ~> A) in f.
  unfold comp at 1 4; simpl.
  unfold Typ.comp.
  extensionality h.
  apply transpose_inv_inj.
  rewrite transpose_inv_l.
  unfold transpose_inv.
  setoid_rewrite <- (comp_id_l (id B)) at 3.
  setoid_rewrite <- fprod_comp.
  rewrite comp_assoc.
  rewrite !eval_transpose.
  reflexivity.
Qed.

Program Definition transpose_from: R ~> L := {|
  transform p f := transpose_inv f;
|}.
Next Obligation.
  rename o1 into A, o2 into C, o into A', o0 into C'.
  destruct f as [f g].
  simpl in *.
  change (A' ~> A) in f.
  unfold comp at 1 4; simpl.
  unfold Typ.comp.
  extensionality h.
  unfold transpose_inv at 1.
  setoid_rewrite <- (comp_id_l (id B)) at 1.
  setoid_rewrite <- fprod_comp.
  rewrite comp_assoc.
  f_equal.
  apply eval_transpose.
Qed.

Lemma transpose_iso_inv_l: transpose_from ∘ transpose_to = id L.
Proof.
  natural_eq p.
  unfold comp; simpl; unfold Typ.comp.
  extensionality f.
  apply transpose_inv_l.
Qed.

Lemma transpose_iso_inv_r: transpose_to ∘ transpose_from = id R.
Proof.
  natural_eq p.
  unfold comp; simpl; unfold Typ.comp.
  extensionality f.
  apply transpose_inv_r.
Qed.

Definition transpose_iso: L <~> R :=
  Isomorphism.Pack transpose_to (Isomorphism.Mixin _ _ _ transpose_to transpose_from transpose_iso_inv_l transpose_iso_inv_r).

End ex4.
