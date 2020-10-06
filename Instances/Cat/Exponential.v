Require Export Instances.Cat.Product.

Definition Exp (T S: Category) := Fun S T.

Program Definition Eval (T S: Category): Exp T S × S ~> T := {|
  fobj p := fst p (snd p);
  fmap (p q: Exp T S × S) f := fst f (snd q) ∘ fmap (fst p) (snd f);
|}.
Next Obligation.
  simpl.
  rewrite comp_id_l.
  apply fmap_id.
Qed.
Next Obligation.
  simpl.
  rewrite <- !comp_assoc.
  f_equal.
  rewrite fmap_comp, !comp_assoc.
  f_equal.
  apply naturality.
Qed.

Program Definition Transpose {T S C: Category} (F: C × S ~> T): C ~> Exp T S := {|
  fobj x := {|
    fobj y := F (x, y);
    fmap a b f := fmap F (id x, f);
  |};
  fmap x y f := {|
    transform a := fmap F (f, id a);
  |}
|}.
Next Obligation.
  f_equal.
  apply (@fmap_id _ _ F).
Qed.
Next Obligation.
  rewrite <- (comp_id_l (id x)) at 1.
  apply (fmap_comp ((id x, f): (_, _) ~> (_, _)) ((id x, g): (_, _) ~> (_, _))).
Qed.
Next Obligation.
  rewrite <- !fmap_comp.
  f_equal.
  apply Prod.hom_eq; simpl; split.
  all: now rewrite comp_id_l, comp_id_r.
Qed.
Next Obligation.
  natural_eq x.
  apply (@fmap_id _ _ F).
Qed.
Next Obligation.
  natural_eq x.
  rewrite <- fmap_comp.
  f_equal.
  unfold comp at 2; simpl.
  f_equal.
  symmetry.
  apply comp_id_l.
Qed.

Lemma Transpose_ump (T S C: Category) (F: C × S ~> T) (G: C ~> Exp T S): Eval T S ∘ (G (×) id S) = F <-> Transpose F = G.
Proof.
  split; intros H.
  + subst F.
    fun_eq x y f.
    fun_eq a b f.
    rewrite fmap_id.
    apply comp_id_l.
    natural_eq a.
    etransitivity.
    etransitivity.
    apply (f_equal (fun f => f ∘ _)).
    3: apply f_equal.
    3: symmetry.
    1, 3: apply is_eq_refl.
    1: apply (transform_is_eq (eq_iso H0)).
    2: apply (transform_is_eq (eq_iso H)).
    1, 2: apply eq_iso_is_eq.
    clear.
    rewrite comp_id_l.
    f_equal.
    apply fmap_id.
  + subst G.
    fun_eq p q f.
    now destruct x.
    destruct p as [x y], q as [x' y'], f as [f g].
    simpl in *.
    rewrite !eq_iso_refl.
    simpl.
    rewrite comp_id_l, comp_id_r.
    rewrite <- fmap_comp.
    f_equal.
    apply Prod.hom_eq; simpl; split.
    apply comp_id_r.
    apply comp_id_l.
Qed.

Definition CatExp_mixin: ExpCategory.mixin_of CatProd :=
  ExpCategory.Mixin CatProd Exp Eval (@Transpose) Transpose_ump.

Canonical CatExp: ExpCategory :=
  ExpCategory.Pack Cat (ExpCategory.Class Cat CatProd_mixin CatExp_mixin).
