Require Export Structure.

Module Eq.

Structure obj {S T: Category} (F G: Functor S T) := Obj {
  sort: S;
  comm: F sort = G sort;
}.

Arguments sort {S T F G} _.
Arguments comm {S T F G} _.
Coercion sort: obj >-> Category.obj.

Lemma obj_eq {S T: Category} {F G: Functor S T} (x y: obj F G): x = y <-> sort x = y.
Proof.
  split.
  intros H.
  now subst y.
  destruct x as [x Hx], y as [y Hy]; simpl.
  intros H.
  subst y.
  f_equal; apply proof_irrelevance.
Qed.

Structure hom {S T: Category} {F G: Functor S T} (x y: obj F G) := {
  map: x ~> y;
  map_comm: eq_iso (comm y) ∘ fmap F map = fmap G map ∘ eq_iso (comm x);
}.

Arguments map {S T F G x y} _.
Arguments map_comm {S T F G x y} _.
Coercion map: hom >-> Categories.hom.

Lemma hom_eq {S T: Category} {F G: Functor S T} {x y: obj F G} (f g: hom x y): f = g <-> map f = g.
Proof.
  split.
  intros H.
  now subst g.
  destruct f as [f Hf], g as [g Hg]; simpl.
  intros H.
  subst g.
  f_equal; apply proof_irrelevance.
Qed.

Section category.
Context {S T: Category} (F G: Functor S T).

Program Definition cat_mixin: Category.mixin_of (obj F G) :=
  Category.Mixin (obj F G) hom
  (fun a => {| map := id a |})
  (fun a b c f g => {| map := f ∘ g |})
  _ _ _.
Next Obligation.
  rewrite !fmap_id, comp_id_l.
  apply comp_id_r.
Qed.
Next Obligation.
  rewrite !fmap_comp, <- comp_assoc, comp_assoc.
  rewrite map_comm, <- comp_assoc.
  f_equal.
  apply map_comm.
Qed.
Next Obligation.
  apply hom_eq; simpl.
  apply comp_assoc.
Qed.
Next Obligation.
  apply hom_eq; simpl.
  apply comp_id_l.
Qed.
Next Obligation.
  apply hom_eq; simpl.
  apply comp_id_r.
Qed.

Canonical cat: Category :=
  Category.Pack (obj F G) cat_mixin.

End category.

Lemma is_eq_map {S T: Category} {F G: Functor S T} {x y: obj F G} (f: hom x y): @is_eq (cat F G) x y f -> is_eq (map f).
Proof.
  intros [e H].
  subst f y.
  rewrite eq_iso_refl; simpl.
  apply is_eq_id.
Qed.

End Eq.

Canonical Eq.cat.
Notation Eq := Eq.cat.

Section CatEq.

Program Definition Ceqz {S T: Category} (F G: Functor S T): Functor (Eq F G) S := {|
  fobj := Eq.sort;
  fmap := @Eq.map S T F G;
|}.

Lemma Ceqz_comm {S T: Category} (F G: Functor S T): F ∘ Ceqz F G = G ∘ Ceqz F G.
Proof.
  fun_eq x y f.
  apply Eq.comm.
  assert (H = Eq.comm x) by apply proof_irrelevance.
  assert (H0 = Eq.comm y) by apply proof_irrelevance.
  subst H H0.
  apply Eq.map_comm.
Qed.

Program Definition EqzMed {E S T: Category} (F G: Functor S T) (e: Functor E S) (He: F ∘ e = G ∘ e): Functor E (Eq F G) := {|
  fobj x := {| Eq.sort := e x; Eq.comm := f_equal (fun F => fobj F x) He |};
  fmap x y f := {| Eq.map := fmap e f; |};
|}.
Next Obligation.
  transitivity (fmap (G ∘ e) f ∘ to (eq_iso He) x).
  transitivity (to (eq_iso He) y ∘ fmap (F ∘ e) f).
  2: apply (naturality (to (eq_iso He))).
  symmetry.
  all: f_equal.
  all: apply is_eq_unique.
  1, 3: apply transform_is_eq.
  all: apply eq_iso_is_eq.
Qed.
Next Obligation.
  apply Eq.hom_eq, fmap_id.
Qed.
Next Obligation.
  apply Eq.hom_eq, fmap_comp.
Qed.

Lemma EqzMed_comm {E S T: Category} (F G: Functor S T) (e: Functor E S) (He: F ∘ e = G ∘ e): Ceqz F G ∘ EqzMed F G e He = e.
Proof.
  now fun_eq x y f.
Qed.

Lemma EqzMed_unique {E S T: Category} (F G: Functor S T) (e: Functor E S) (u: Functor E (Eq F G)) (He: F ∘ e = G ∘ e): Ceqz F G ∘ u = e -> EqzMed F G e He = u.
Proof.
  intros H.
  subst e.
  fun_eq x y f.
  now apply Eq.obj_eq.
  apply Eq.hom_eq; simpl.
  transitivity (Eq.map (fmap u f)).
  2: symmetry.
  1: rewrite <- comp_id_l.
  2: rewrite <- comp_id_r.
  all: f_equal.
  all: apply is_eq_refl.
  apply (Eq.is_eq_map (to (eq_iso H0))), eq_iso_is_eq.
  apply (Eq.is_eq_map (to (eq_iso H))), eq_iso_is_eq.
Qed.

Definition CatEq_mixin: EqCategory.mixin_of Cat :=
  EqCategory.Mixin Cat (@Eq) (@Ceqz) (@Ceqz_comm) (@EqzMed) (@EqzMed_comm) (@EqzMed_unique).

Canonical CatEq: EqCategory :=
  EqCategory.Pack Cat CatEq_mixin.
End CatEq.
