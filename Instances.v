Require Export Instances.Cat.
Require Export Instances.Dual.
Require Import Categories.DArrow.

Lemma monic_is_faithful {S T: Category} (F: S ~> T): monic F -> faithful F.
Proof.
  intros HF x y f g H.
  specialize (HF DArrow (DArrow.F f) (DArrow.F g)).
  assert (F ∘ DArrow.F f = F ∘ DArrow.F g).
  fun_eq a b u.
  now destruct a, b, u.
  specialize (HF H0); clear H0.
  apply fun_eq, proj2 in HF.
  specialize (HF false true tt eq_refl eq_refl).
  simpl in HF.
  now rewrite comp_id_l, comp_id_r in HF.
Qed.
