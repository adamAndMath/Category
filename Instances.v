Require Export Instances.Cat.
Require Import Categories.DArrow.

Lemma fmap_monic_inj {S T: Category} {x y: S} (F: S ~> T) (f g: x ~> y): monic F -> fmap F f = fmap F g -> f = g.
Proof.
  intros HF fg.
  specialize (HF DArrow (DArrow.F f) (DArrow.F g)).
  assert (F ∘ DArrow.F f = F ∘ DArrow.F g).
  fun_eq a b u.
  now destruct a, b, u.
  specialize (HF H); clear H fg.
  apply fun_eq, proj2 in HF.
  specialize (HF false true tt eq_refl eq_refl).
  simpl in HF.
  rewrite comp_id_l, comp_id_r in HF.
  exact HF.
Qed.
