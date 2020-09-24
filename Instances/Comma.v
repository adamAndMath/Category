Require Export Structure.

Module Comma.

Section Category.
Context {A B C: Category} (S: A ~> C) (T: B ~> C).

Structure obj := Obj {
  source: A;
  target: B;
  morph: S source ~> T target;
}.

Lemma obj_eq (x y: obj): x = y <-> source x = source y /\ target x = target y /\ (forall (Hs: source x = source y) (Ht: target x = target y), (fmap T (eq_iso Ht)) ∘ morph x = morph y ∘ (fmap S (eq_iso Hs))).
Proof.
  split.
  + intros H.
    subst y.
    repeat split.
    intros Hs Ht.
    rewrite !eq_iso_refl.
    simpl.
    rewrite !fmap_id.
    rewrite comp_id_r.
    apply comp_id_l.
  + destruct x as [xs xt x], y as [ys yt y].
    simpl.
    intros [Hs [Ht H]].
    subst ys yt.
    f_equal.
    specialize (H eq_refl eq_refl).
    simpl in H.
    rewrite !fmap_id in H.
    rewrite comp_id_l, comp_id_r in H.
    exact H.
Qed.

Structure hom (x y: obj) := Hom {
  smap: source x ~> source y;
  tmap: target x ~> target y;
  comm: fmap T tmap ∘ morph x = morph y ∘ fmap S smap;
}.

Arguments smap {x y} _.
Arguments tmap {x y} _.

Lemma hom_eq {x y: obj} (f g: hom x y): f = g <-> smap f = smap g /\ tmap f = tmap g.
Proof.
  split.
  intros H.
  now subst g.
  destruct f as [f1 f2 Hf], g as [g1 g2 Hg]; simpl.
  intros [H1 H2].
  subst g1 g2.
  f_equal.
  apply proof_irrelevance.
Qed.

Program Definition id (x: obj): hom x x := {|
  smap := id (source x);
  tmap := id (target x);
|}.
Next Obligation.
  rewrite !fmap_id.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Program Definition comp {x y z: obj} (g: hom y z) (f: hom x y): hom x z := {|
  smap := smap g ∘ smap f;
  tmap := tmap g ∘ tmap f;
|}.
Next Obligation.
  rewrite !fmap_comp.
  rewrite comp_assoc, <- comp_assoc.
  rewrite comm.
  rewrite comp_assoc.
  f_equal.
  apply comm.
Qed.

Lemma comp_id_l {x y: obj} (f: hom x y): comp (id y) f = f.
Proof.
  apply hom_eq; simpl; split.
  all: apply comp_id_l.
Qed.

Lemma comp_id_r {x y: obj} (f: hom x y): comp f (id x) = f.
Proof.
  apply hom_eq; simpl; split.
  all: apply comp_id_r.
Qed.

Lemma comp_assoc {a b c d: obj} (h: hom c d) (g: hom b c) (f: hom a b): comp h (comp g f) = comp (comp h g) f.
Proof.
  apply hom_eq; simpl; split.
  all: apply comp_assoc.
Qed.

Definition cat_mixin: Category.mixin_of obj :=
  Category.Mixin obj hom id (@comp) (@comp_assoc) (@comp_id_l) (@comp_id_r).

Canonical cat := Category.Pack obj cat_mixin.

End Category.

Arguments source {A B C S T} _.
Arguments target {A B C S T} _.
Arguments morph {A B C S T} _.

Arguments smap {A B C S T x y} _.
Arguments tmap {A B C S T x y} _.

Local Infix "↓" := cat (at level 60, no associativity).

Definition Source {A B C: Category} {S: A ~> C} {T: B ~> C}: S ↓ T ~> A := {|
  fobj := source;
  fmap := @smap A B C S T;
  fmap_id _ := eq_refl;
  fmap_comp _ _ _ _ _ := eq_refl;
|}.

Definition Target {A B C: Category} {S: A ~> C} {T: B ~> C}: S ↓ T ~> B := {|
  fobj := target;
  fmap := @tmap A B C S T;
  fmap_id _ := eq_refl;
  fmap_comp _ _ _ _ _ := eq_refl;
|}.

Lemma smap_is_eq {A B C: Category} (S: A ~> C) {T: B ~> C} (x y: S ↓ T) (f: x ~> y): is_eq f -> is_eq (smap f).
Proof.
  intros [e H].
  subst f y.
  apply is_eq_id.
Qed.

Lemma tmap_is_eq {A B C: Category} (S: A ~> C) {T: B ~> C} (x y: S ↓ T) (f: x ~> y): is_eq f -> is_eq (tmap f).
Proof.
  intros [e H].
  subst f y.
  apply is_eq_id.
Qed.

End Comma.

Notation Comma := Comma.cat.
Infix "↓" := Comma (at level 60, no associativity).
