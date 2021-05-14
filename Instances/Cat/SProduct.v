Require Export Structure.

Module SProd.

Section category.
Context {I} (F: I -> Category).

Program Definition cat_mixin :=
  Category.Mixin (forall i, F i)
  (fun f g => forall i, f i ~> g i)
  (fun f i => id (f i))
  (fun x y z f g i => f i ∘ g i)
  _ _ _.
Next Obligation.
  extensionality i.
  apply comp_assoc.
Qed.
Next Obligation.
  extensionality i.
  apply comp_id_l.
Qed.
Next Obligation.
  extensionality i.
  apply comp_id_r.
Qed.

Definition cat: Category :=
  Category.Pack (forall i, F i) cat_mixin.

Lemma obj_eq (p q: cat): p = q <-> forall i, p i = q i.
Proof.
  split.
  now intros [].
  intros H.
  now extensionality i.
Qed.

Lemma hom_eq {p q: cat} (f g: p ~> q): f = g <-> forall i, f i = g i.
Proof.
  split.
  now intros [].
  intros H.
  now extensionality i.
Qed.

End category.

End SProd.

Notation SProd := SProd.cat.

Section CatSProd.

Program Definition CatSProd_mixin := SProdCategory.Mixin Cat (@SProd)
  (fun I S T F => {|
    fobj x i := F i x;
    fmap x Y f i := fmap (F i) f;
  |})
  (fun I C i => {|
    fobj x := x i;
    fmap x y f := f i;
  |})
  _.
Next Obligation.
  extensionality i.
  apply fmap_id.
Qed.
Next Obligation.
  extensionality i.
  apply fmap_comp.
Qed.
Next Obligation.
  split.
  + intros H.
    subst g.
    intros i.
    now fun_eq x y g.
  + intros H.
    apply functional_extensionality_dep in H.
    subst f.
    fun_eq x y f.
    rewrite !eq_iso_refl; simpl.
    rewrite comp_id_r.
    apply comp_id_l.
Qed.

Canonical CatSProd := SProdCategory.Pack Cat CatSProd_mixin.

End CatSProd.

Program Definition CatSProd_Top_mixin {I} (C: I -> TopCategory) := TopCategory.Mixin (SProd C)
  (fun i => 1) (fun f i => !) _.
Next Obligation.
  extensionality i.
  apply to_one_unique.
Qed.

Canonical CatSProd_Top {I} (C: I -> TopCategory): TopCategory :=
  TopCategory.Pack (SProd C) (CatSProd_Top_mixin C).
