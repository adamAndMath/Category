Require Export Categories.Poset.
Require Export Instances.
Require Export Congruence.
Require Export Instances.Dual.
Require Export Categories.Typ.

Lemma ex1 (C: Category): is_proset C -> exists D, is_poset D /\ C ≈ D.
Proof.
  intros H.
  exists (Poset.strict_pro (Proset.conn C)); split.
  exact (Poset_correct (Poset.strict_po (Proset.conn C))).
  transitivity (Proset.conn C).
  apply iso_cequiv.
  symmetry.
  now apply proset_ex.
  generalize (Proset.conn C); clear C H.
  intros P.
  exists (Proset.hom_func (Poset.strict_unit P)).
  apply is_equiv_alt; split.
  + intros x y f.
    unshelve eexists.
    2: split; intros; apply Proset.chom_eq.
    now apply f; simpl.
  + intros X.
    destruct (Poset.strictObj_surj X) as [x HX].
    subst X.
    now exists x.
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
    setoid_rewrite fprod_comp.
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
  setoid_rewrite fprod_comp.
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
  unfold comp at 1; simpl.
  rewrite !comp_assoc, <- comp_assoc.
  f_equal.
  rewrite <- fprod_comp.
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
  symmetry.
  extensionality h.
  rewrite comp_assoc.
  f_equal.
  apply transpose_inv_inj.
  rewrite transpose_inv_l.
  unfold transpose_inv at 1 3.
  setoid_rewrite <- (comp_id_l (id B)).
  setoid_rewrite fprod_comp.
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
  extensionality h.
  apply transpose_inv_inj.
  rewrite transpose_inv_l.
  unfold transpose_inv.
  setoid_rewrite <- (comp_id_l (id B)) at 3.
  setoid_rewrite fprod_comp.
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
  extensionality h.
  unfold transpose_inv at 1.
  setoid_rewrite <- (comp_id_l (id B)) at 1.
  setoid_rewrite fprod_comp.
  rewrite comp_assoc.
  f_equal.
  apply eval_transpose.
Qed.

Lemma transpose_iso_inv_l: transpose_from ∘ transpose_to = id L.
Proof.
  natural_eq p.
  unfold comp; simpl.
  extensionality f.
  apply transpose_inv_l.
Qed.

Lemma transpose_iso_inv_r: transpose_to ∘ transpose_from = id R.
Proof.
  natural_eq p.
  unfold comp; simpl.
  extensionality f.
  apply transpose_inv_r.
Qed.

Definition transpose_iso: L <~> R :=
  Isomorphism.Pack transpose_to (Isomorphism.Mixin _ _ _ transpose_to transpose_from transpose_iso_inv_l transpose_iso_inv_r).

End ex4.
