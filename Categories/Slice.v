Require Export Structure.

Module Slice.

Structure obj (C: Category) (c: C) := Obj {
  dom: C;
  arr: dom ~> c;
}.

Arguments dom {C c} o.
Arguments arr {C c} o.

Structure hom {C: Category} {c: C} (f g: obj C c) := Hom {
  map: dom f ~> dom g;
  comm: arr g ∘ map = arr f;
}.

Arguments Hom {C c f g} map comm.
Arguments map {C c f g} _.
Arguments comm {C c f g} _.
Coercion map: hom >-> Categories.hom.

Lemma obj_eq {C: Category} {c: C} {f g: obj C c}: f = g <-> dom f = dom g /\ (forall e: dom f = dom g, arr f = arr g ∘ eq_iso e).
Proof.
  split.
  + intros H.
    subst g.
    repeat split.
    intros e.
    rewrite eq_iso_refl.
    symmetry.
    apply comp_id_r.
  + destruct f as [x f], g as [x' g].
    simpl.
    intros [Hx H].
    subst x'.
    f_equal.
    rewrite <- comp_id_r.
    exact (H eq_refl).
Qed.

Lemma hom_eq {C: Category} {c: C} {f g: obj C c} (a b: hom f g): a = b <-> map a = map b.
Proof.
  split.
  intros H.
  now subst b.
  destruct a as [a Ha], b as [b Hb].
  simpl.
  intros H.
  subst b.
  f_equal.
  apply proof_irrelevance.
Qed.

Program Definition cat_mixin (C: Category) (c: C) := Category.Mixin (obj C c) hom
  (fun f => {|
    map := id (dom f);
    comm := comp_id_r (arr f);
  |})
  (fun f g h a b => {|
    map := a ∘ b;
    comm := eq_trans (comp_assoc _ _ _) (eq_trans (f_equal (fun f => f ∘ _) (comm a)) (comm b));
  |})
  _ _ _.
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

Canonical cat (C: Category) (c: C): Category :=
  Category.Pack (obj C c) (cat_mixin C c).

Program Canonical Dom (C: Category) (c: C): cat C c ~> C := {|
  fobj := dom;
  fmap := @map C c;
|}.

Definition img {C: Category} {x y: C} (f: x ~> y) (p: obj C x) := {|
  dom := dom p;
  arr := f ∘ arr p;
|}.

Program Definition img_map {C: Category} {x y: C} (f: x ~> y) {p q: obj C x} (g: p ~> q): img f p ~> img f q := {|
  map := map g;
|}.
Next Obligation.
  rewrite <- comp_assoc.
  f_equal.
  apply comm.
Qed.

Program Canonical Img {C: Category} {x y: C} (f: x ~> y): Functor (cat C x) (cat C y) := {|
  fobj := img f;
  fmap := @img_map C x y f;
|}.
Next Obligation.
  now apply hom_eq.
Qed.
Next Obligation.
  now apply hom_eq.
Qed.

Program Definition preimg {C: PullCategory} {x y: C} (f: y ~> x) (p: obj C x): obj C y := {|
  dom := Pull f (arr p);
  arr := pull1 f (arr p);
|}.

Program Definition preimg_map {C: PullCategory} {x y: C} (f: y ~> x) {p q: obj C x} (g: p ~> q): preimg f p ~> preimg f q := {|
  map := pull_med f (arr q) (pull1 f (arr p)) (map g ∘ pull2 f (arr p)) _;
|}.
Next Obligation.
  rewrite pull_comm, comp_assoc.
  f_equal.
  symmetry.
  apply comm.
Qed.
Next Obligation.
  apply pull_med1.
Qed.

Program Canonical Preimg {C: PullCategory} {x y: C} (f: y ~> x): Functor (cat C x) (cat C y) := {|
  fobj := preimg f;
  fmap := @preimg_map C x y f;
|}.
Next Obligation.
  apply hom_eq; simpl.
  apply pull_med_unique.
  2: rewrite comp_id_l.
  all: apply comp_id_r.
Qed.
Next Obligation.
  apply hom_eq; simpl.
  apply pull_med_unique.
  all: rewrite comp_assoc.
  rewrite pull_med1.
  apply pull_med1.
  rewrite pull_med2.
  rewrite <- !comp_assoc.
  f_equal.
  apply pull_med2.
Qed.

Program Definition img_unit {C: PullCategory} {x y: C} (f: x ~> y) (p: obj C x): p ~> preimg f (img f p) := {|
  map := pull_med f (f ∘ arr p) (arr p) (id (dom p)) _;
|}.
Next Obligation.
  symmetry.
  apply comp_id_r.
Qed.
Next Obligation.
  apply pull_med1.
Qed.

Program Canonical imgU {C: PullCategory} {x y: C} (f: x ~> y): id (cat C x) ~> Preimg f ∘ Img f := {|
  transform := img_unit f;
|}.
Next Obligation.
  rename x0 into p, y0 into q, f0 into g.
  apply hom_eq; simpl.
  transitivity (pull_med f (f ∘ arr q) (arr q ∘ g) g (comp_assoc f (arr q) g)).
  symmetry.
  all: apply pull_med_unique.
  all: rewrite !comp_assoc.
  2: rewrite <- comp_id_l.
  1, 2: f_equal.
  apply pull_med1.
  apply pull_med2.
  rewrite !pull_med1.
  symmetry.
  apply comm.
  rewrite pull_med2.
  rewrite <- comp_assoc, <- comp_id_r.
  f_equal.
  apply pull_med2.
Qed.

Program Definition img_counit {C: PullCategory} {x y: C} (f: x ~> y) (p: obj C y): img f (preimg f p) ~> p := {|
  map := pull2 f (arr p);
|}.
Next Obligation.
  symmetry.
  apply pull_comm.
Qed.

Program Canonical imgCU {C: PullCategory} {x y: C} (f: x ~> y): Img f ∘ Preimg f ~> id (cat C y) := {|
  transform := img_counit f;
|}.
Next Obligation.
  rename x0 into p, y0 into q, f0 into g.
  apply hom_eq; simpl.
  apply pull_med2.
Qed.

Lemma img_adjoint {C: PullCategory} {x y: C} (f: x ~> y): adjoint_by (Img f) (Preimg f) (imgU f) (imgCU f).
Proof.
  apply adjoint_by_alt.
  split.
  + intros p.
    apply hom_eq; simpl.
    apply pull_med2.
  + intros p.
    apply hom_eq; simpl.
    transitivity (pull_med f (arr p) (pull1 f (arr p)) (pull2 f (arr p)) (pull_comm f (arr p))).
    symmetry.
    all: apply pull_med_unique.
    3, 4: apply comp_id_r.
    all: rewrite comp_assoc.
    rewrite pull_med1.
    apply pull_med1.
    rewrite pull_med2.
    rewrite <- comp_assoc.
    rewrite pull_med2.
    apply comp_id_r.
Qed.

End Slice.

Canonical Slice.cat.
Canonical Slice.Dom.
Canonical Slice.Img.
Canonical Slice.Preimg.
Canonical Slice.imgU.
Canonical Slice.imgCU.
Coercion Slice.map: Slice.hom >-> hom.
Notation Slice := Slice.cat.
Infix "/" := Slice.

Module Coslice.

Structure obj (C: Category) (c: C) := Obj {
  cod: C;
  arr: c ~> cod;
}.

Arguments cod {C c} o.
Arguments arr {C c} o.

Structure hom {C: Category} {c: C} (f g: obj C c) := Hom {
  map: cod f ~> cod g;
  comm: map ∘ arr f = arr g;
}.

Arguments Hom {C c f g} map comm.
Arguments map {C c f g} _.
Arguments comm {C c f g} _.
Coercion map: hom >-> Categories.hom.

Lemma obj_eq {C: Category} {c: C} {f g: obj C c}: f = g <-> cod f = cod g /\ (forall e: cod f = cod g, eq_iso e ∘ arr f = arr g).
Proof.
  split.
  + intros H.
    subst g.
    repeat split.
    intros e.
    rewrite eq_iso_refl.
    apply comp_id_l.
  + destruct f as [x f], g as [x' g].
    simpl.
    intros [Hx H].
    subst x'.
    f_equal.
    rewrite <- (comp_id_l f).
    exact (H eq_refl).
Qed.

Lemma hom_eq {C: Category} {c: C} {f g: obj C c} (a b: hom f g): a = b <-> map a = map b.
Proof.
  split.
  intros H.
  now subst b.
  destruct a as [a Ha], b as [b Hb].
  simpl.
  intros H.
  subst b.
  f_equal.
  apply proof_irrelevance.
Qed.

Program Definition cat_mixin (C: Category) (c: C) := Category.Mixin (obj C c) hom
  (fun f => {|
    map := id (cod f);
    comm := comp_id_l (arr f);
  |})
  (fun f g h a b => {|
    map := a ∘ b;
    comm := eq_trans (eq_sym (comp_assoc _ _ _)) (eq_trans (f_equal (fun f => _ ∘ f) (comm b)) (comm a));
  |})
  _ _ _.
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

Canonical cat (C: Category) (c: C): Category :=
  Category.Pack (obj C c) (cat_mixin C c).

Program Canonical Cod (C: Category) (c: C): cat C c ~> C := {|
  fobj := cod;
  fmap := @map C c;
|}.

Definition preimg {C: Category} {x y: C} (f: y ~> x) (p: obj C x) := {|
  cod := cod p;
  arr := arr p ∘ f;
|}.

Program Definition preimg_map {C: Category} {x y: C} (f: y ~> x) {p q: obj C x} (g: p ~> q): preimg f p ~> preimg f q := {|
  map := map g;
|}.
Next Obligation.
  rewrite comp_assoc.
  f_equal.
  apply comm.
Qed.

Program Canonical Preimg {C: Category} {x y: C} (f: y ~> x): Functor (cat C x) (cat C y) := {|
  fobj := preimg f;
  fmap := @preimg_map C x y f;
|}.
Next Obligation.
  now apply hom_eq.
Qed.
Next Obligation.
  now apply hom_eq.
Qed.

End Coslice.

Canonical Coslice.cat.
Canonical Coslice.Cod.
Canonical Coslice.Preimg.
Coercion Coslice.map: Coslice.hom >-> hom.
Notation Coslice := Coslice.cat.
Infix "\" := Coslice (at level 40, left associativity).
