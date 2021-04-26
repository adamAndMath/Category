Require Export Limit.

Module CatColimit.
Section cat.
Universes i j i' j'.
Context {I: Category@{i j}}.

Structure obj (F: Functor I Cat@{i' i j j'}): Type@{i} := Obj {
  index: I;
  elm: F index;
}.

Arguments index {F} _.
Arguments elm {F} _.

Context {F: Functor I Cat@{i' i j j'}}.

Lemma obj_eq (X Y: obj F): X = Y <-> index X = index Y /\ forall e: index X = index Y, fmap F (eq_iso e) (elm X) = elm Y.
Proof.
  split.
  + intros []; clear Y.
    split.
    reflexivity.
    intros e.
    rewrite eq_iso_refl; simpl.
    now rewrite fmap_id.
  + destruct X as [X x], Y as [Y y]; simpl.
    intros [e H].
    subst Y.
    f_equal.
    specialize (H eq_refl); simpl in H.
    rewrite fmap_id in H.
    exact H.
Qed.

Structure hom (X Y: obj F): Type@{j} := Hom {
  map: index X ~> index Y;
  emap: fmap F map (elm X) ~> elm Y;
}.

Arguments map {X Y} _.
Arguments emap {X Y} _.

Lemma hom_eq {X Y: obj F} (f g: hom X Y): f = g <-> map f = map g /\ forall e: map f = map g, emap f = emap g ∘ to (eq_iso (f_equal (fmap F) e)) (elm X).
Proof.
  split.
  + intros H.
    subst g; split.
    reflexivity.
    intros e.
    rewrite eq_iso_refl; simpl.
    symmetry.
    apply comp_id_r.
  + destruct f as [f f'], g as [g g']; simpl.
    intros [e H].
    subst g.
    f_equal.
    rewrite <- comp_id_r.
    apply (H eq_refl).
Qed.

Definition id (X: obj F): hom X X := {|
  map := id (index X);
  emap := to (eq_iso (@fmap_id _ _ F (index X))) (elm X);
|}.

Definition comp {X Y Z: obj F} (f: hom Y Z) (g: hom X Y): hom X Z := {|
  map := map f ∘ map g;
  emap := emap f ∘ fmap (fmap F (map f)) (emap g) ∘ to (eq_iso (@fmap_comp _ _ F _ _ _ (map f) (map g))) (elm X);
|}.

Lemma comp_id_l {X Y: obj F} (f: hom X Y): comp (id Y) f = f.
Proof.
  apply hom_eq; simpl; split.
  apply comp_id_l.
  intros e.
  etransitivity.
  apply (f_equal (fun f => f ∘ _)).
  apply (naturality (to (eq_iso (@fmap_id I Cat F (index Y))))).
  rewrite <- comp_assoc.
  f_equal.
  apply is_eq_unique.
  apply is_eq_comp.
  apply (transform_is_eq (eq_iso (@fmap_comp _ _ F _ _ _ (Categories.id (index Y)) (map f))) (elm X)), eq_iso_is_eq.
  apply transform_is_eq, eq_iso_is_eq.
  apply (transform_is_eq (eq_iso (f_equal (fmap F) e))), eq_iso_is_eq.
Qed.

Lemma comp_id_r {X Y: obj F} (f: hom X Y): comp f (id X) = f.
Proof.
  apply hom_eq; simpl; split.
  apply comp_id_r.
  intros e.
  rewrite <- comp_assoc.
  f_equal.
  apply is_eq_unique.
  apply is_eq_comp.
  apply (transform_is_eq (eq_iso (@fmap_comp _ _ F _ _ _ (map f) (Categories.id (index X)))) (elm X)), eq_iso_is_eq.
  apply fmap_is_eq, (transform_is_eq (eq_iso (@fmap_id I Cat F (index X)))), eq_iso_is_eq.
  apply (transform_is_eq (eq_iso (f_equal (fmap F) e))), eq_iso_is_eq.
Qed.

Lemma comp_assoc {X Y Z W: obj F} (f: hom Z W) (g: hom Y Z) (h: hom X Y): comp f (comp g h) = comp (comp f g) h.
Proof.
  apply hom_eq; simpl; split.
  apply comp_assoc.
  intros e.
  rewrite !(@fmap_comp _ _ (fmap F (map f))).
  rewrite <- !comp_assoc.
  do 2 f_equal.
  rewrite comp_assoc.
  symmetry.
  etransitivity.
  apply (f_equal (fun f => f ∘ _)).
  apply (naturality (to (eq_iso (@fmap_comp _ _ F _ _ _ (map f) (map g))))).
  rewrite <- comp_assoc.
  f_equal.
  apply is_eq_unique; repeat apply is_eq_comp.
  apply transform_is_eq, eq_iso_is_eq.
  4: apply (fmap_is_eq (fmap F (map f))).
  all: apply (transform_is_eq (eq_iso (@fmap_comp I Cat F _ _ _ _ _))), eq_iso_is_eq.
Qed.

Definition cat_mixin := Category.Mixin (obj F) hom id (@comp) (@comp_assoc) (@comp_id_l) (@comp_id_r).
Canonical cat := Category.Pack (obj F) cat_mixin.

Program Definition Into (X: I): Functor (F X) cat := {|
  fobj x := {| index := X; elm := x |};
  fmap x y f := {| map := Categories.id X; emap := f ∘ to (eq_iso (@fmap_id I Cat F X)) x |};
|}.
Next Obligation.
  apply hom_eq; simpl; split.
  reflexivity.
  intros e.
  rewrite eq_iso_refl; clear e; simpl.
  rewrite Categories.comp_id_r.
  apply Categories.comp_id_l.
Qed.
Next Obligation.
  apply hom_eq; simpl; split.
  symmetry.
  apply Categories.comp_id_l.
  intros e.
  rewrite <- !(Categories.comp_assoc f).
  f_equal.
  symmetry.
  rewrite (@fmap_comp _ _ (fmap F (Categories.id X))), Categories.comp_assoc.
  etransitivity.
  apply (f_equal (fun f => f ∘ _ ∘ _ ∘ _)).
  apply (naturality (to (eq_iso (@fmap_id I Cat F X)))).
  simpl.
  rewrite <- !(Categories.comp_assoc g).
  f_equal.
  apply is_eq_unique.
  repeat apply is_eq_comp.
  apply transform_is_eq, eq_iso_is_eq.
  apply (transform_is_eq (eq_iso (@fmap_comp I Cat F _ _ _ _ _))), eq_iso_is_eq.
  apply fmap_is_eq.
  all: apply (transform_is_eq (eq_iso (@fmap_id I Cat F X))), eq_iso_is_eq.
Qed.

Program Definition into: Natural F (Δ cat) := {|
  transform x := Into x;
|}.
Next Obligation.
  rewrite Categories.comp_id_l.
  fun_eq a b g.


End cat.

End CatColimit.
