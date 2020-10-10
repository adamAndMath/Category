Require Export Structure.

Definition repr {A} (R: A -> A -> Prop) (x: A): A :=
  epsilon (inhabits x) (R x).

Lemma repr_correct {A} (R: A -> A -> Prop) {RE: Equivalence R} (x: A): R x (repr R x).
Proof.
  unfold repr.
  apply epsilon_spec.
  now exists x.
Qed.

Lemma repr_idem {A} (R: A -> A -> Prop) {RE: Equivalence R} (x: A): repr R (repr R x) = repr R x.
Proof.
  unfold repr.
  generalize (inhabits (epsilon (inhabits x) (R x))).
  intros.
  f_equal.
  apply proof_irrelevance.
  clear i.
  extensionality y.
  apply propositional_extensionality.
  change (R (repr R x) y <-> R x y).
  f_equiv.
  symmetry.
  apply repr_correct, RE.
Qed.

Lemma repr_eq {A} (R: A -> A -> Prop) {RE: Equivalence R} (x y: A): repr R x = repr R y <-> R x y.
Proof.
  split; intros H.
  + rewrite (repr_correct R).
    rewrite H.
    symmetry.
    apply repr_correct, RE.
  + unfold repr.
    f_equal.
    apply proof_irrelevance.
    extensionality z.
    apply propositional_extensionality.
    now f_equiv.
Qed.

Structure Quotient {A} (R: A -> A -> Prop) := {
  elm: A;
  elm_is_repr: repr R elm = elm;
}.

Arguments elm {A R} _.
Arguments elm_is_repr {A R} _.

Definition quotient {A} (R: A -> A -> Prop) {RE: Equivalence R} (x: A): Quotient R := {|
  elm := repr R x;
  elm_is_repr := repr_idem R x;
|}.

Lemma Quotient_eq {A} (R: A -> A -> Prop) {RE: Equivalence R} (x y: Quotient R): x = y <-> R (elm x) (elm y).
Proof.
  split; intros H.
  now subst y.
  destruct x as [x Hx], y as [y Hy].
  simpl in H.
  apply (repr_eq R) in H.
  rewrite Hx, Hy in H.
  subst y.
  f_equal.
  apply proof_irrelevance.
Qed.

Definition arrow_rel (C: Category) := forall X Y: C, X ~> Y -> X ~> Y -> Prop.

Declare Scope cong_scope.
Delimit Scope cong_scope with cong.
Bind Scope cong_scope with arrow_rel.

Class Congruence {C: Category} (R: arrow_rel C) := {
  cong_equiv (X Y: C) :> Equivalence (R X Y);
  cong_comp (X Y Z: C) :> Proper (R Y Z ==> R X Y ==> R X Z) comp;
}.

Definition cong_le {C: Category} (R Q: arrow_rel C) :=
  forall x y f g, R x y f g -> Q x y f g.

Infix "<=" := cong_le: cong_scope.

Instance cong_preorder (C: Category): PreOrder (@cong_le C).
Proof.
  split.
  easy.
  intros R1 R2 R3 H1 H2 x y f g H.
  apply H2, H1, H.
Qed.

Definition fcong {S T: Category} (F: S ~> T) (x y: S) (f g: x ~> y) := fmap F f = fmap F g.
Arguments fcong {S T} F x y (f g) /.
Infix "~[ F ]" := (fcong F _ _) (at level 70, no associativity).

Instance fcong_correct {S T: Category} (F: S ~> T): Congruence (fcong F).
Proof.
  split.
  intros x y; split.
  + intros f.
    now simpl.
  + intros f g.
    now simpl.
  + intros f g h.
    simpl.
    intros H1 H2.
    now transitivity (fmap F g).
  + intros x y z f f' Hf g g' Hg.
    simpl.
    rewrite !fmap_comp.
    now f_equal.
Qed.

Module Cong.
Section category.
Context {C: Category} (R: arrow_rel C) {Con: Congruence R}.

Let obj := Category.obj C.

Structure hom (x y: obj) := Hom {
  p1: x ~> y;
  p2: x ~> y;
  congruent: R _ _ p1 p2;
}.

Lemma hom_eq {x y: obj} (f g: hom x y): f = g <-> p1 _ _ f = p1 _ _ g /\ p2 _ _ f = p2 _ _ g.
Proof.
  split.
  intros H.
  now subst g.
  destruct f as [f1 f2 Hf], g as [g1 g2 Hg].
  simpl.
  intros [H1 H2].
  subst g1 g2.
  f_equal.
  apply proof_irrelevance.
Qed.

Definition id (x: obj):hom x x := {|
  p1 := id x;
  p2 := id x;
  congruent := reflexivity (id x);
|}.

Definition comp {x y z: obj} (f: hom y z) (g: hom x y): hom x z := {|
  p1 := p1 _ _ f ∘ p1 _ _ g;
  p2 := p2 _ _ f ∘ p2 _ _ g;
  congruent := cong_comp x y z _ _ (congruent _ _ f) _ _ (congruent _ _ g);
|}.

Lemma comp_assoc {a b c d: obj} (f: hom c d) (g: hom b c) (h: hom a b): comp f (comp g h) = comp (comp f g) h.
Proof.
  apply hom_eq; simpl; split.
  all: apply comp_assoc.
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

Definition cat_mixin: Category.mixin_of obj :=
  Category.Mixin obj hom id (@comp) (@comp_assoc) (@comp_id_l) (@comp_id_r).

Definition cat := Category.Pack obj cat_mixin.

Program Definition P1: cat ~> C := {|
  fobj x := x;
  fmap := p1;
  fmap_id _ := eq_refl;
  fmap_comp _ _ _ _ _ := eq_refl;
|}.

Program Definition P2: cat ~> C := {|
  fobj x := x;
  fmap := p2;
  fmap_id _ := eq_refl;
  fmap_comp _ _ _ _ _ := eq_refl;
|}.

End category.

End Cong.

Notation Cong := Cong.cat.

Module Quot.
Section category.
Context {C: Category} (R: arrow_rel C) {Con: Congruence R}.

Let obj := Category.obj C.
Let hom (x y: obj) := Quotient (R x y).

Lemma hom_eq {x y: obj} (f g: hom x y): f = g <-> R x y (elm f) (elm g).
Proof. exact (Quotient_eq (R x y) f g). Qed.

Definition id (x: obj): hom x x := quotient _ (id x).
Definition comp {x y z: obj} (f: hom y z) (g: hom x y): hom x z := quotient _ (elm f ∘ elm g).

Lemma comp_assoc {a b c d: obj} (f: hom c d) (g: hom b c) (h: hom a b): comp f (comp g h) = comp (comp f g) h.
Proof.
  apply hom_eq; simpl.
  rewrite <- !(repr_correct _).
  rewrite comp_assoc.
  reflexivity.
Qed.

Lemma comp_id_l {x y: obj} (f: hom x y): comp (id y) f = f.
Proof.
  apply hom_eq; simpl.
  rewrite <- !(repr_correct _).
  rewrite comp_id_l.
  reflexivity.
Qed.

Lemma comp_id_r {x y: obj} (f: hom x y): comp f (id x) = f.
Proof.
  apply hom_eq; simpl.
  rewrite <- !(repr_correct _).
  rewrite comp_id_r.
  reflexivity.
Qed.

Definition cat_mixin: Category.mixin_of obj :=
  Category.Mixin obj hom id (@comp) (@comp_assoc) (@comp_id_l) (@comp_id_r).

Definition cat := Category.Pack obj cat_mixin.

Program Definition into: C ~> cat := {|
  fobj x := x;
  fmap x y := quotient _;
|}.
Next Obligation.
  apply hom_eq; simpl.
  rewrite <- !(repr_correct _).
  reflexivity.
Qed.

End category.

Program Definition fact {S T: Category} (F: S ~> T) (R: arrow_rel S) {Con: Congruence R} (H: (R <= fcong F)%cong): cat R ~> T := {|
  fobj := F;
  fmap x y f := fmap F (elm f);
|}.
Next Obligation.
  rewrite <- fmap_id.
  apply H.
  symmetry.
  apply (repr_correct _).
Qed.
Next Obligation.
  rewrite <- fmap_comp.
  apply H.
  symmetry.
  apply (repr_correct _).
Qed.

End Quot.

Notation Quot := Quot.cat.

Lemma cong_coeq {C: Category} (R: arrow_rel C) {Con: Congruence R}: is_coequalizer (Cong.P1 R) (Cong.P2 R) (Quot R) (Quot.into R).
Proof.
  split.
  + fun_eq x y f.
    rewrite !eq_iso_refl.
    simpl.
    rewrite comp_id_l, comp_id_r.
    apply (Quot.hom_eq R); simpl.
    rewrite <- !(repr_correct _).
    apply Cong.congruent.
  + intros Z F HF.
    apply fun_eq, proj2 in HF.
    specialize (fun x y f => HF x y f eq_refl eq_refl).
    simpl in HF.
    setoid_rewrite comp_id_l in HF.
    setoid_rewrite comp_id_r in HF.
    specialize (fun x y f g H => HF x y (Cong.Hom R x y f g H)).
    simpl in HF.
    unshelve eexists.
    unshelve eexists.
    exact F.
    exact (fun x y f => fmap F (elm f)).
    3: split.
    4: intros G HG.
    3, 4: fun_eq x y f.
    1, 2: simpl.
    intros x.
    rewrite <- fmap_id.
    apply HF.
    symmetry.
    apply (repr_correct (R x x)).
    intros x y z f g.
    rewrite <- fmap_comp.
    apply HF.
    symmetry.
    apply (repr_correct (R x z)).
    apply HF.
    symmetry.
    apply (repr_correct (R x y)).
    1, 2: subst F.
    reflexivity.
    simpl in HF.
    rewrite !eq_iso_refl.
    simpl.
    rewrite comp_id_l, comp_id_r.
    f_equal.
    apply (Quot.hom_eq R); simpl.
    symmetry.
    apply (repr_correct (R x y)).
Qed.

Definition ker {S T: Category} (F: S ~> T) := Cong (fcong F).
Definition fqout {S T: Category} (F: S ~> T) := Quot (fcong F).

Lemma fcong_factor {S T: Category} (F: S ~> T) (R: arrow_rel S) {Con: Congruence R}: (R <= fcong F)%cong <-> exists! G: Quot R ~> T, G ∘ Quot.into R = F.
Proof.
  split.
  + intros HF.
    exists (Quot.fact F R HF).
    split.
    fun_eq x y f.
    apply HF.
    symmetry.
    apply (repr_correct _).
    intros G HG.
    symmetry in HG.
    apply fun_eq in HG; simpl in HG.
    fun_eq x y f.
    apply HG.
    apply proj2 in HG.
    specialize (HG x y (elm f) H H0).
    revert HG.
    change (?P -> ?Q) with (impl P Q).
    f_equiv.
    do 2 f_equal.
    apply (Quot.hom_eq _).
    simpl.
    symmetry.
    apply (repr_correct _).
  + intros [G [HF _]] x y f g H.
    subst F.
    simpl.
    f_equal.
    apply (Quot.hom_eq _).
    simpl.
    rewrite <- !(repr_correct _).
    exact H.
Qed.

Lemma factor_fun {S T: Category} (F: S ~> T): Quot.fact F (fcong F) (reflexivity (fcong F)) ∘ Quot.into (fcong F) = F.
Proof.
  fun_eq x y f.
  change (repr (fcong F x y) f ~[F] f).
  symmetry.
  apply (repr_correct _).
Qed.
