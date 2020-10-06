Require Export Structure.
Require Export Instances.Typ.

Section Properties.
Context {C: CartCategory} {S: C} (op: S × S ~> S).

Definition assoc :=
  op ∘ (id S (×) op) = op ∘ (op (×) id S) ∘ prod_associator S S S.

Definition comm :=
  op ∘ Product.flip S S = op.

Definition left_unit (u: 1 ~> S) :=
  op ∘ ⟨u ∘ to_one, id S⟩ = id S.

Definition right_unit (u: 1 ~> S) :=
  op ∘ ⟨id S, u ∘ to_one⟩ = id S.

Lemma gen_assoc: assoc <-> forall (Z: C) (f g h: Z ~> S), op ∘ ⟨f, op ∘ ⟨g, h⟩⟩ = op ∘ ⟨op ∘ ⟨f, g⟩, h⟩.
Proof.
  unfold assoc.
  rewrite gen_eq_r.
  split; intros H Z; intros.
  + specialize (H Z ⟨f, ⟨g, h⟩⟩).
    simpl in H.
    unfold prod_associator_to in H.
    rewrite <- !comp_assoc in H.
    rewrite !fork_comp in H.
    rewrite <- !comp_assoc in H.
    rewrite !pi2_fork, !pi1_fork in H.
    rewrite !fprod_fork in H.
    rewrite !comp_id_l in H.
    exact H.
  + assert (exists f g h: Z ~> S, ⟨f, ⟨g, h⟩⟩ = a).
      exists (π₁ ∘ a), (π₁ ∘ π₂ ∘ a), (π₂ ∘ π₂ ∘ a).
      rewrite <- !fork_comp.
      rewrite fork_id.
      rewrite comp_id_l.
      rewrite fork_id.
      apply comp_id_l.
    destruct H0 as [f [g [h H0]]].
    subst a.
    specialize (H Z f g h).
    simpl.
    unfold prod_associator_to.
    rewrite <- !comp_assoc.
    rewrite !fork_comp.
    rewrite <- !comp_assoc.
    rewrite !pi2_fork, !pi1_fork.
    rewrite !fprod_fork.
    rewrite !comp_id_l.
    exact H.
Qed.

Lemma gen_comm: comm <-> forall (Z: C) (f g: Z ~> S), op ∘ ⟨f, g⟩ = op ∘ ⟨g, f⟩.
Proof.
  unfold comm.
  rewrite gen_eq_r.
  split; intros H Z; intros.
  + specialize (H Z ⟨g, f⟩).
    unfold Product.flip in H.
    rewrite <- comp_assoc in H.
    rewrite fork_comp in H.
    rewrite pi1_fork, pi2_fork in H.
    exact H.
  + assert (exists f g: Z ~> S, ⟨f, g⟩ = a).
      exists (π₁ ∘ a), (π₂ ∘ a).
      rewrite <- fork_comp.
      rewrite fork_id.
      apply comp_id_l.
    destruct H0 as [f [g H0]].
    subst a.
    specialize (H Z g f).
    unfold Product.flip.
    rewrite <- comp_assoc.
    rewrite fork_comp.
    rewrite pi1_fork, pi2_fork.
    exact H.
Qed.

Lemma gen_unit_l (u: 1 ~> S): left_unit u <-> forall (Z: C) (f: Z ~> S), op ∘ ⟨u ∘ to_one, f⟩ = f.
Proof.
  unfold left_unit.
  rewrite gen_eq_r.
  enough (forall (Z: C) (f: Z ~> S), op ∘ ⟨u ∘ to_one, id S⟩ ∘ f = id S ∘ f <-> op ∘ ⟨u ∘ to_one, f⟩ = f).
  split; intros H0 Z f.
  1, 2: apply H, H0.
  intros Z f.
  rewrite <- comp_assoc.
  rewrite fork_comp.
  rewrite <- comp_assoc.
  rewrite !comp_id_l.
  setoid_rewrite <- (to_one_unique (to_one ∘ f)).
  reflexivity.
Qed.

Lemma gen_unit_r (u: 1 ~> S): right_unit u <-> forall (Z: C) (f: Z ~> S), op ∘ ⟨f, u ∘ to_one⟩ = f.
Proof.
  unfold right_unit.
  rewrite gen_eq_r.
  enough (forall (Z: C) (f: Z ~> S), op ∘ ⟨id S, u ∘ to_one⟩ ∘ f = id S ∘ f <-> op ∘ ⟨f, u ∘ to_one⟩ = f).
  split; intros H0 Z f.
  1, 2: apply H, H0.
  intros Z f.
  rewrite <- comp_assoc.
  rewrite fork_comp.
  rewrite <- comp_assoc.
  rewrite !comp_id_l.
  setoid_rewrite <- (to_one_unique (to_one ∘ f)).
  reflexivity.
Qed.

End Properties.

Module Monoid.

Structure obj (C: CartCategory) := Obj {
  base: C;
  law: base × base ~> base;
  unit: 1 ~> base;
  law_assoc: assoc law;
  law_unit_l: left_unit law unit;
  law_unit_r: right_unit law unit;
}.

Arguments base {C} _.
Arguments law {C} _.
Arguments unit {C} _.
Arguments law_assoc {C} _.
Arguments law_unit_l {C} _.
Arguments law_unit_r {C} _.

Structure hom {C: CartCategory} (G H: obj C) := Hom {
  arr: base G ~> base H;
  arr_law: arr ∘ law G = law H ∘ (arr (×) arr);
  arr_unit: arr ∘ unit G = unit H;
}.

Arguments arr {C G H} _.
Arguments arr_law {C G H} _.
Arguments arr_unit {C G H} _.

Lemma obj_eq_full {C: CartCategory} (A B: obj C): A = B <-> base A = base B /\ (forall e: base A = base B, eq_iso e ∘ law A = law B ∘ (eq_iso e (×) eq_iso e)) /\ (forall e: base A = base B, eq_iso e ∘ unit A = unit B).
Proof.
  split.
  + intros H.
    subst B.
    repeat split.
    all: intros e.
    all: rewrite eq_iso_refl.
    all: clear e.
    all: simpl.
    rewrite fprod_id, comp_id_r.
    all: apply comp_id_l.
  + destruct A as [A m um], B as [B n un].
    simpl.
    intros [H [Hlaw Hunit]].
    subst B.
    specialize (Hunit eq_refl).
    specialize (Hlaw eq_refl).
    simpl in Hunit, Hlaw.
    rewrite fprod_id, comp_id_r in Hlaw.
    rewrite comp_id_l in Hunit.
    rewrite comp_id_l in Hlaw.
    subst n un.
    f_equal.
    all: apply proof_irrelevance.
Qed.

Lemma obj_eq {C: CartCategory} (A B: obj C): A = B <-> base A = base B /\ (forall e: base A = base B, eq_iso e ∘ law A = law B ∘ (eq_iso e (×) eq_iso e)).
Proof.
  rewrite obj_eq_full.
  destruct A as [x mx ux mx_assoc mx_ux_l mx_ux_r].
  destruct B as [y my uy my_assoc my_uy_l my_uy_r].
  simpl.
  split.
  + intros [H [Hl _]].
    now split.
  + intros [H Hl].
    repeat split.
    1, 2: assumption.
    clear H.
    intros H.
    specialize (Hl H).
    subst y.
    simpl in Hl |- *.
    rewrite fprod_id, comp_id_l, comp_id_r in Hl.
    subst my.
    rewrite comp_id_l.
    rewrite gen_unit_l in my_uy_l.
    rewrite <- (my_uy_l _ ux).
    rewrite gen_unit_r in mx_ux_r.
    rewrite <- mx_ux_r.
    rewrite (to_one_unique (id 1)).
    rewrite !comp_id_r.
    reflexivity.
Qed.

Lemma hom_eq {C: CartCategory} {G H: obj C} (f g: hom G H): f = g <-> arr f = arr g.
Proof.
  split; intros.
  now subst g.
  destruct f as [f], g as [g].
  simpl in *.
  subst g.
  f_equal.
  all: apply proof_irrelevance.
Qed.

Module cat.

Section Def.
Context {C: CartCategory}.

Program Definition id (G: obj C): hom G G := {|
  arr := id (base G);
|}.
Next Obligation.
  rewrite fprod_id, comp_id_r.
  apply comp_id_l.
Qed.
Next Obligation.
  apply comp_id_l.
Qed.

Program Definition comp {A B C: obj C} (f: hom B C) (g: hom A B): hom A C := {|
  arr := arr f ∘ arr g;
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite arr_law.
  rewrite comp_assoc.
  rewrite arr_law.
  rewrite <- comp_assoc.
  f_equal.
  apply fprod_comp.
Qed.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite arr_unit.
  apply arr_unit.
Qed.

Lemma comp_assoc {a b c d: obj C} (f: hom c d) (g: hom b c) (h: hom a b): comp f (comp g h) = comp (comp f g) h.
Proof.
  apply hom_eq; simpl.
  apply comp_assoc.
Qed.

Lemma comp_id_l {G H: obj C} (f: hom G H): comp (id H) f = f.
Proof.
  apply hom_eq; simpl.
  apply comp_id_l.
Qed.

Lemma comp_id_r {G H: obj C} (f: hom G H): comp f (id G) = f.
Proof.
  apply hom_eq; simpl.
  apply comp_id_r.
Qed.

Program Definition one: obj C := {|
  base := 1;
  law := to_one;
  unit := to_one;
|}.
Next Obligation.
  apply gen_assoc.
  intros Z f g h.
  transitivity (@to_one C Z).
  symmetry.
  all: apply to_one_unique.
Qed.
Next Obligation.
  red.
  transitivity (@to_one C 1).
  symmetry.
  all: apply to_one_unique.
Qed.
Next Obligation.
  red.
  transitivity (@to_one C 1).
  symmetry.
  all: apply to_one_unique.
Qed.

Program Definition to_one {G: obj C}: hom G one := {|
  arr := to_one;
|}.
Next Obligation.
  transitivity (@to_one C (base G × base G)).
  symmetry.
  all: apply to_one_unique.
Qed.
Next Obligation.
  symmetry.
  apply to_one_unique.
Qed.

Lemma to_one_unique {G: obj C} (f: hom G one): to_one = f.
Proof.
  apply hom_eq.
  apply to_one_unique.
Qed.

Program Definition prod (A B: obj C): obj C := {|
  base := base A × base B;
  law := (law A (×) law B) ∘ ⟨⟨π₁ ∘ π₁, π₁ ∘ π₂⟩, ⟨π₂ ∘ π₁, π₂ ∘ π₂⟩⟩;
  unit := ⟨unit A, unit B⟩;
|}.
Next Obligation.
  apply gen_assoc.
  intros Z f g h.
  rewrite !fprod_fork.
  rewrite !fork_comp.
  f_equal.
  all: rewrite <- !Categories.comp_assoc.
  all: rewrite !fork_comp.
  all: rewrite <- !Categories.comp_assoc.
  all: rewrite !pi1_fork, !pi2_fork.
  rewrite pi1_fork.
  all: apply gen_assoc, law_assoc.
Qed.
Next Obligation.
  red.
  rewrite fprod_fork, fork_comp.
  rewrite <- !Categories.comp_assoc.
  rewrite !fork_comp.
  rewrite <- !Categories.comp_assoc.
  rewrite !pi1_fork, !pi2_fork.
  rewrite !Categories.comp_assoc.
  rewrite pi1_fork, pi2_fork.
  rewrite !Categories.comp_id_r.
  setoid_rewrite (proj1 (gen_unit_l _ _) (law_unit_l _)).
  apply fork_id.
Qed.
Next Obligation.
  red.
  rewrite fprod_fork, fork_comp.
  rewrite <- !Categories.comp_assoc.
  rewrite !fork_comp.
  rewrite <- !Categories.comp_assoc.
  rewrite !pi1_fork, !pi2_fork.
  rewrite !Categories.comp_assoc.
  rewrite pi1_fork, pi2_fork.
  rewrite !Categories.comp_id_r.
  setoid_rewrite (proj1 (gen_unit_r _ _) (law_unit_r _)).
  apply fork_id.
Qed.

Program Definition fork {G H I: obj C} (f: hom G H) (g: hom G I): hom G (prod H I) := {|
  arr := ⟨arr f, arr g⟩;
|}.
Next Obligation.
  rewrite fprod_fork.
  rewrite !fork_comp.
  unfold fprod.
  f_equal.
  all: rewrite <- Categories.comp_assoc.
  all: rewrite !fork_comp.
  all: rewrite <- !Categories.comp_assoc.
  all: rewrite pi2_fork, pi1_fork.
  1: rewrite !pi1_fork.
  2: rewrite !pi2_fork.
  all: apply arr_law.
Qed.
Next Obligation.
  rewrite fork_comp.
  f_equal.
  all: apply arr_unit.
Qed.

Program Definition pi1 {A B: obj C}: hom (prod A B) A := {|
  arr := π₁;
|}.
Next Obligation.
  rewrite fprod_fork.
  apply pi1_fork.
Qed.
Next Obligation.
  apply pi1_fork.
Qed.

Program Definition pi2 {A B: obj C}: hom (prod A B) B := {|
  arr := π₂;
|}.
Next Obligation.
  rewrite fprod_fork.
  apply pi2_fork.
Qed.
Next Obligation.
  apply pi2_fork.
Qed.

Lemma fork_pi {G H I: obj C} (f: hom G H) (g: hom G I) (h: hom G (prod H I)): h = fork f g <-> comp pi1 h = f /\ comp pi2 h = g.
Proof.
  rewrite !hom_eq; simpl.
  apply fork_pi.
Qed.

End Def.

End cat.

Section structure.
Context (C: CartCategory).

Definition cat_mixin: Category.mixin_of (obj C) :=
  Category.Mixin (obj C) (@hom C) (cat.id) (@cat.comp C) (@cat.comp_assoc C) (@cat.comp_id_l C) (@cat.comp_id_r C).

Canonical cat: Category :=
  Category.Pack (obj C) cat_mixin.

Definition top_mixin: TopCategory.mixin_of cat :=
  TopCategory.Mixin cat cat.one (@cat.to_one C) (@cat.to_one_unique C).

Canonical top: TopCategory :=
  TopCategory.Pack cat top_mixin.

Definition prod_mixin: ProdCategory.mixin_of cat :=
  ProdCategory.Mixin cat cat.prod (@cat.fork C) (@cat.pi1 C) (@cat.pi2 C) (@cat.fork_pi C).

Canonical prod: ProdCategory :=
  ProdCategory.Pack cat prod_mixin.

Canonical cart: CartCategory :=
  CartCategory.Pack cat (CartCategory.Class cat top_mixin prod_mixin).

End structure.

Program Definition Base {C: CartCategory}: cat C ~> C := {|
  fobj := base;
  fmap := @arr C;
|}.

Program Definition Flatten {C: CartCategory}: cat (cart C) ~> cat C := {|
  fobj G := {|
    base := base (base G);
    law := arr (law G);
    unit := arr (unit G);
  |};
  fmap A B f := {|
    arr := arr (arr f);
  |}
|}.
Next Obligation.
  specialize (law_assoc G) as H.
  apply hom_eq in H.
  exact H.
Qed.
Next Obligation.
  specialize (law_unit_l G) as H.
  apply hom_eq in H.
  exact H.
Qed.
Next Obligation.
  specialize (law_unit_r G) as H.
  apply hom_eq in H.
  exact H.
Qed.
Next Obligation.
  specialize (arr_law f) as H.
  apply hom_eq in H.
  exact H.
Qed.
Next Obligation.
  specialize (arr_unit f) as H.
  apply hom_eq in H.
  exact H.
Qed.
Next Obligation.
  now apply hom_eq.
Qed.
Next Obligation.
  now apply hom_eq.
Qed.

Lemma flatten_is_base {C: CartCategory} (G: cat (cart C)): Flatten G = base G.
Proof.
  enough (forall (Z: C) (f g h i: Z ~> base (base G)),
    law (Flatten G) ∘ ⟨law (base G) ∘ ⟨f, g⟩, law (base G) ∘ ⟨h, i⟩⟩ =
    law (base G) ∘ ⟨law (Flatten G) ∘ ⟨f, h⟩, law (Flatten G) ∘ ⟨g, i⟩⟩
  ).
  enough (unit (Flatten G) = unit (base G)).
  apply obj_eq; simpl; split.
  reflexivity.
  intros e.
  rewrite eq_iso_refl.
  simpl.
  rewrite fprod_id, comp_id_r, comp_id_l.
  + apply gen_eq_r.
    intros Z a.
    assert (exists f g, ⟨f, g⟩ = a).
      exists (π₁ ∘ a), (π₂ ∘ a).
      rewrite <- fork_comp, fork_id.
      apply comp_id_l.
    destruct H1 as [f [g]].
    subst a.
    symmetry.
    rewrite <- (proj1 (gen_unit_r _ _) (law_unit_r (Flatten G)) _ f) at 1.
    rewrite <- (proj1 (gen_unit_l _ _) (law_unit_l (Flatten G)) _ g) at 1.
    rewrite <- H.
    rewrite H0.
    rewrite (proj1 (gen_unit_l _ _) (law_unit_l (base G))).
    rewrite (proj1 (gen_unit_r _ _) (law_unit_r (base G))).
    reflexivity.
  + rewrite <- (comp_id_r (unit (Flatten G))).
    rewrite <- (comp_id_r (unit (base G))).
    rewrite <- (to_one_unique (id 1)).
    rewrite <- (proj1 (gen_unit_l _ _) (law_unit_l (Flatten G)) _ (unit (Flatten G) ∘ _)).
    rewrite <- (proj1 (gen_unit_l _ _) (law_unit_l (base G)) _ (unit (Flatten G) ∘ _)) at 1.
    rewrite <- (proj1 (gen_unit_r _ _) (law_unit_r (base G)) _ (unit (Flatten G) ∘ _)) at 2.
    rewrite H.
    rewrite (proj1 (gen_unit_l _ _) (law_unit_l (Flatten G))).
    rewrite (proj1 (gen_unit_r _ _) (law_unit_r (Flatten G))).
    apply (proj1 (gen_unit_l _ _) (law_unit_l (base G))).
  + intros Z f g h i.
    specialize (arr_law (law G)) as H.
    rewrite gen_eq_r in H.
    specialize (H Z ⟨⟨f, h⟩, ⟨g, i⟩⟩).
    simpl in H.
    rewrite <- !comp_assoc in H.
    rewrite !fork_comp in H.
    rewrite <- !comp_assoc in H.
    rewrite !pi1_fork, !pi2_fork, pi1_fork in H.
    rewrite !fprod_fork in H.
    exact H.
Qed.

End Monoid.

Canonical Monoid.cat.
Canonical Monoid.top.
Canonical Monoid.prod.
Canonical Monoid.cart.
Notation Monoid := Monoid.cart.

Definition Mon := Monoid TypCart.

Definition is_monoid (C: Category) :=
  exists u: C, forall x: C, u = x.

Module AbMonoid.

Structure obj (C: CartCategory) := Obj {
  base: C;
  law: base × base ~> base;
  unit: 1 ~> base;
  law_assoc: assoc law;
  law_comm: comm law;
  law_unit_l: left_unit law unit;
}.

Arguments base {C} _.
Arguments law {C} _.
Arguments unit {C} _.
Arguments law_assoc {C} _.
Arguments law_comm {C} _.
Arguments law_unit_l {C} _.

Structure hom {C: CartCategory} (G H: obj C) := Hom {
  arr: base G ~> base H;
  arr_law: arr ∘ law G = law H ∘ (arr (×) arr);
  arr_unit: arr ∘ unit G = unit H;
}.

Arguments arr {C G H} _.
Arguments arr_law {C G H} _.
Arguments arr_unit {C G H} _.

Lemma obj_eq {C: CartCategory} (A B: obj C): A = B <-> base A = base B /\ (forall e: base A = base B, eq_iso e ∘ law A = law B ∘ (eq_iso e (×) eq_iso e)).
Proof.
  split.
  + intros H.
    subst B.
    repeat split.
    intros e.
    rewrite eq_iso_refl.
    simpl.
    rewrite fprod_id, comp_id_r.
    apply comp_id_l.
  + destruct A as [x mx ux mx_assoc mx_comm mx_ux_l].
    destruct B as [y my uy my_assoc my_comm my_uy_l].
    simpl.
    intros [Hx Hm].
    subst y.
    specialize (Hm eq_refl).
    simpl in Hm.
    rewrite fprod_id, comp_id_l, comp_id_r in Hm.
    subst my.
    enough (ux = uy).
    subst uy.
    f_equal; apply proof_irrelevance.
    rewrite gen_unit_l in my_uy_l.
    rewrite <- (my_uy_l _ ux).
    rewrite gen_unit_l in mx_ux_l.
    rewrite <- mx_ux_l.
    rewrite (to_one_unique (id 1)).
    rewrite !comp_id_r.
    rewrite gen_comm in mx_comm.
    apply mx_comm.
Qed.

Lemma hom_eq {C: CartCategory} {G H: obj C} (f g: hom G H): f = g <-> arr f = arr g.
Proof.
  split; intros.
  now subst g.
  destruct f as [f], g as [g].
  simpl in *.
  subst g.
  f_equal.
  all: apply proof_irrelevance.
Qed.

Module cat.

Section Def.
Context {C: CartCategory}.

Program Definition id (G: obj C): hom G G := {|
  arr := id (base G);
|}.
Next Obligation.
  rewrite fprod_id, comp_id_r.
  apply comp_id_l.
Qed.
Next Obligation.
  apply comp_id_l.
Qed.

Program Definition comp {A B C: obj C} (f: hom B C) (g: hom A B): hom A C := {|
  arr := arr f ∘ arr g;
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite arr_law.
  rewrite comp_assoc.
  rewrite arr_law.
  rewrite <- comp_assoc.
  f_equal.
  apply fprod_comp.
Qed.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite arr_unit.
  apply arr_unit.
Qed.

Lemma comp_assoc {a b c d: obj C} (f: hom c d) (g: hom b c) (h: hom a b): comp f (comp g h) = comp (comp f g) h.
Proof.
  apply hom_eq; simpl.
  apply comp_assoc.
Qed.

Lemma comp_id_l {G H: obj C} (f: hom G H): comp (id H) f = f.
Proof.
  apply hom_eq; simpl.
  apply comp_id_l.
Qed.

Lemma comp_id_r {G H: obj C} (f: hom G H): comp f (id G) = f.
Proof.
  apply hom_eq; simpl.
  apply comp_id_r.
Qed.

End Def.

End cat.

Definition cat_mixin (C: CartCategory): Category.mixin_of (obj C) :=
  Category.Mixin (obj C) (@hom C) (cat.id) (@cat.comp C) (@cat.comp_assoc C) (@cat.comp_id_l C) (@cat.comp_id_r C).

Canonical cat (C: CartCategory): Category :=
  Category.Pack (obj C) (cat_mixin C).

Section Theory.
Context {C: CartCategory}.

Program Definition mon (M: obj C): Monoid.obj C := {|
  Monoid.base := base M;
  Monoid.law := law M;
  Monoid.unit := unit M;
|}.
Next Obligation.
  apply law_assoc.
Qed.
Next Obligation.
  apply law_unit_l.
Qed.
Next Obligation.
  red.
  rewrite (proj1 (gen_comm _) (law_comm M)).
  apply law_unit_l.
Qed.

Program Definition Mon: cat C ~> Monoid C := {|
  fobj M := mon M;
  fmap M N f := {|
    Monoid.arr := arr f;
    Monoid.arr_law := arr_law f;
    Monoid.arr_unit := arr_unit f;
  |}
|}.
Next Obligation.
  now apply Monoid.hom_eq.
Qed.
Next Obligation.
  now apply Monoid.hom_eq.
Qed.

Program Definition Base: cat C ~> C := {|
  fobj := base;
  fmap := @arr C;
|}.

End Theory.

End AbMonoid.

Canonical AbMonoid.cat.
Notation AbMonoid := AbMonoid.cat.

Definition AbMon := AbMonoid TypCart.

Definition is_abmonoid (C: Category) :=
  exists u: C, (forall x: C, u = x) /\ (forall f g: u ~> u, f ∘ g = g ∘ f).

Section DoubleMonoid.
Context (C: CartCategory).

Program Definition DoubleMonoid_to: Monoid (Monoid C) ~> AbMonoid C := {|
  fobj G := {|
    AbMonoid.base := Monoid.base (Monoid.base G);
    AbMonoid.law := Monoid.law (Monoid.base G);
    AbMonoid.unit := Monoid.unit (Monoid.base G);
  |};
  fmap A B f := {|
    AbMonoid.arr := Monoid.arr (Monoid.arr f);
  |}
|}.
Next Obligation.
  apply Monoid.law_assoc.
Qed.
Next Obligation.
  specialize (Monoid.flatten_is_base G) as H.
  apply Monoid.obj_eq_full, proj2 in H.
  simpl in H.
  destruct H as [Hl Hu].
  specialize (Hl eq_refl).
  specialize (Hu eq_refl).
  simpl in Hl, Hu.
  rewrite fprod_id, comp_id_l, comp_id_r in Hl.
  rewrite comp_id_l in Hu.
  destruct G as [G [m] [u] G_assoc G_unit_l G_unit_r].
  simpl in *.
  subst m u.
  clear - arr_law.
  rename arr_law into H.
  rewrite gen_eq_r in H.
  apply gen_comm.
  intros Z f g.
  specialize (H Z ⟨⟨Monoid.unit G ∘ to_one, g⟩, ⟨f, Monoid.unit G ∘ to_one⟩⟩).
  rewrite <- !comp_assoc in H.
  rewrite !fork_comp in H.
  rewrite <- !comp_assoc in H.
  rewrite !pi1_fork, !pi2_fork, pi1_fork in H.
  rewrite !fprod_fork in H.
  rewrite !(proj1 (gen_unit_l _ _) (Monoid.law_unit_l G)) in H.
  rewrite !(proj1 (gen_unit_r _ _) (Monoid.law_unit_r G)) in H.
  exact H.
Qed.
Next Obligation.
  apply Monoid.law_unit_l.
Qed.
Next Obligation.
  apply Monoid.arr_law.
Qed.
Next Obligation.
  apply Monoid.arr_unit.
Qed.
Next Obligation.
  now apply AbMonoid.hom_eq.
Qed.
Next Obligation.
  now apply AbMonoid.hom_eq.
Qed.

Program Definition DoubleMonoid_from: AbMonoid C ~> Monoid (Monoid C) := {|
  fobj G := {|
    Monoid.base := AbMonoid.mon G;
    Monoid.law := {|
      Monoid.arr := AbMonoid.law G;
    |};
    Monoid.unit := {|
      Monoid.arr := AbMonoid.unit G;
    |}
  |};
  fmap A B f := {|
    Monoid.arr := fmap AbMonoid.Mon f;
  |}
|}.
Next Obligation.
  rewrite fprod_fork.
  rewrite (proj1 (gen_assoc _) (AbMonoid.law_assoc G)).
  rewrite (proj1 (gen_comm _) (AbMonoid.law_comm G) _ _ (π₂ ∘ π₁)).
  rewrite (proj1 (gen_assoc _) (AbMonoid.law_assoc G)).
  rewrite <- (proj1 (gen_assoc _) (AbMonoid.law_assoc G)).
  rewrite (proj1 (gen_comm _) (AbMonoid.law_comm G) _ (π₂ ∘ π₁)).
  rewrite <- !fork_comp, fork_id, !comp_id_l.
  reflexivity.
Qed.
Next Obligation.
  rewrite <- (comp_id_r (AbMonoid.unit G)).
  rewrite <- (to_one_unique (id 1)).
  apply gen_unit_l, AbMonoid.law_unit_l.
Qed.
Next Obligation.
  rewrite <- (proj1 (gen_unit_l _ _) (AbMonoid.law_unit_l G) _ (AbMonoid.unit G)) at 1.
  rewrite <- comp_assoc.
  f_equal.
  unfold fprod.
  rewrite fork_comp, <- comp_assoc.
  do 2 f_equal.
  etransitivity.
  symmetry.
  all: apply to_one_unique.
Qed.
Next Obligation.
  rewrite (to_one_unique (id 1)).
  apply comp_id_r.
Qed.
Next Obligation.
  apply Monoid.hom_eq; simpl.
  apply AbMonoid.law_assoc.
Qed.
Next Obligation.
  apply Monoid.hom_eq; simpl.
  apply AbMonoid.law_unit_l.
Qed.
Next Obligation.
  apply Monoid.hom_eq; simpl.
  rewrite (proj1 (gen_comm _) (AbMonoid.law_comm G)).
  apply AbMonoid.law_unit_l.
Qed.
Next Obligation.
  apply Monoid.hom_eq; simpl.
  apply AbMonoid.arr_law.
Qed.
Next Obligation.
  apply Monoid.hom_eq; simpl.
  apply AbMonoid.arr_unit.
Qed.
Next Obligation.
  now do 2 apply Monoid.hom_eq.
Qed.
Next Obligation.
  now do 2 apply Monoid.hom_eq.
Qed.

Lemma DoubleMonoid_inv_l: DoubleMonoid_from ∘ DoubleMonoid_to = id (Monoid (Monoid C)).
Proof.
  fun_eq x y f.
  apply Monoid.obj_eq; simpl; split.
  apply Monoid.obj_eq; simpl; split.
  reflexivity.
  intros e.
  rewrite eq_iso_refl; clear e.
  simpl.
  rewrite fprod_id, comp_id_l, comp_id_r.
  reflexivity.
  intros e.
  apply Monoid.hom_eq; simpl.
  etransitivity.
  etransitivity.
  apply (f_equal (fun f => f ∘ _)).
  3: apply f_equal.
  3: symmetry.
  1, 3: apply is_eq_refl.
  1, 2: destruct e; simpl.
  apply is_eq_id.
  rewrite !comp_id_l, fork_id.
  apply is_eq_id.
  rewrite comp_id_l, comp_id_r.
  clear e.
  specialize (Monoid.flatten_is_base x) as H.
  apply Monoid.obj_eq, proj2 in H.
  specialize (H eq_refl).
  simpl in H.
  rewrite fprod_id, comp_id_l, comp_id_r in H.
  now symmetry.
  apply Monoid.hom_eq; simpl.
  apply Monoid.hom_eq; simpl.
  etransitivity.
  etransitivity.
  apply (f_equal (fun f => f ∘ _)).
  3: apply f_equal.
  3: symmetry.
  1, 3: apply is_eq_refl.
  1: destruct H0.
  2: destruct H.
  1, 2: apply is_eq_id.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Lemma DoubleMonoid_inv_r: DoubleMonoid_to ∘ DoubleMonoid_from = id (AbMonoid C).
Proof.
  fun_eq x y f.
  apply AbMonoid.obj_eq; simpl; split.
  reflexivity.
  intros e.
  rewrite eq_iso_refl; clear e.
  simpl.
  rewrite fprod_id, comp_id_l, comp_id_r.
  reflexivity.
  apply AbMonoid.hom_eq; simpl.
  etransitivity.
  etransitivity.
  apply (f_equal (fun f => f ∘ _)).
  3: apply f_equal.
  3: symmetry.
  1, 3: apply is_eq_refl.
  1: destruct H0.
  2: destruct H.
  1, 2: apply is_eq_id.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Definition DoubleMonoid: Monoid (Monoid C) <~> AbMonoid C :=
  Isomorphism.Pack DoubleMonoid_to (Isomorphism.Mixin _ _ _ DoubleMonoid_to DoubleMonoid_from DoubleMonoid_inv_l DoubleMonoid_inv_r).

Lemma double_monoid: Monoid (Monoid C) ≃ AbMonoid C.
Proof.
  constructor.
  exact DoubleMonoid.
Qed.

End DoubleMonoid.
