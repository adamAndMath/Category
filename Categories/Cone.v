Require Export Base.

Module Cone.

Section category.
Context {S T: Category} (F: S ~> T).

Structure obj := Obj {
  vertex: T;
  edge x: vertex ~> F x;
  edge_comm x y (f: x ~> y): fmap F f ∘ edge x = edge y;
}.

Lemma obj_eq (N L: obj): N = L <-> vertex N = vertex L /\ (forall (x: S) (e: vertex N = vertex L), edge N x = edge L x ∘ eq_iso e).
Proof.
  split.
  + intros H.
    subst L.
    split.
    reflexivity.
    intros x e.
    rewrite eq_iso_refl.
    symmetry.
    apply comp_id_r.
  + destruct N as [v1 e1 H1], L as [v2 e2 H2].
    simpl.
    intros [Hv He].
    subst v2.
    assert (e1 = e2).
    extensionality x.
    rewrite <- comp_id_r.
    exact (He x eq_refl).
    subst e2.
    f_equal.
    apply proof_irrelevance.
Qed.

Structure hom (N L: obj) := Hom {
  mediator: vertex N ~> vertex L;
  mediator_comm x: edge L x ∘ mediator = edge N x;
}.

Lemma hom_eq {N L: obj} (f g: hom N L): f = g <-> (mediator _ _ f = mediator _ _ g).
Proof.
  split; intros H.
  now subst g.
  destruct f as [f Hf], g as [g Hg].
  simpl in H.
  subst g.
  f_equal.
  apply proof_irrelevance.
Qed.

Ltac hom_eq :=
  match goal with
  | [ |- ?f = ?g] =>
    apply (hom_eq f g);
    simpl
  end.

Definition id (c: obj): hom c c := {|
  mediator := id (vertex c);
  mediator_comm x := comp_id_r (edge c x);
|}.

Definition comp {X Y Z: obj} (f: hom Y Z) (g: hom X Y): hom X Z := {|
  mediator := mediator _ _ f ∘ mediator _ _ g;
  mediator_comm x := eq_trans (comp_assoc _ _ _)
    (eq_trans (f_equal2 _ (mediator_comm _ _ f x) eq_refl) (mediator_comm _ _ g x));
|}.

Lemma comp_assoc {A B C D: obj} (f: hom C D) (g: hom B C) (h: hom A B): comp f (comp g h) = comp (comp f g) h.
Proof.
  hom_eq.
  apply comp_assoc.
Qed.

Lemma comp_id_l {X Y: obj} (f: hom X Y): comp (id Y) f = f.
Proof.
  hom_eq.
  apply comp_id_l.
Qed.

Lemma comp_id_r {X Y: obj} (f: hom X Y): comp f (id X) = f.
Proof.
  hom_eq.
  apply comp_id_r.
Qed.

Definition cat_mixin: Category.mixin_of obj :=
  Category.Mixin obj hom id (@comp) (@comp_assoc) (@comp_id_l) (@comp_id_r).

Definition cat: Category :=
  Category.Pack obj cat_mixin.

End category.

Arguments vertex {_ _ _} _.
Arguments edge {_ _ _} _ _.
Arguments edge_comm {_ _ _} _ {_ _} _.

Arguments mediator {_ _ _ _ _} _.
Arguments mediator_comm {_ _ _ _ _} _ _.

Coercion mediator: hom >-> Categories.hom.

Ltac hom_eq :=
  match goal with
  | [ |- ?f = ?g] =>
    apply (hom_eq _ f g);
    simpl
  end.

Lemma mediator_is_eq {S T: Category} {F: S ~> T} {x y: cat F} (f: x ~> y): is_eq f -> is_eq (mediator f).
Proof.
  intros [e H].
  subst f y.
  simpl.
  apply is_eq_id.
Qed.

End Cone.

Coercion Cone.mediator: Cone.hom >-> Categories.hom.
Canonical Cone.cat.

Notation Cone := Cone.cat.

Definition nat_cone {S T: Category} {F: S ~> T} (c: Cone F): Δ (Cone.vertex c) ~> F := {|
  transform := Cone.edge c: forall x, Δ (Cone.vertex c) x ~> F x;
  naturality x y f := eq_trans (comp_id_r _) (eq_sym (Cone.edge_comm c f));
|}.

Definition cone_nat {S T: Category} {F: S ~> T} (c: T) (η: Δ c ~> F): Cone F := {|
  Cone.vertex := c;
  Cone.edge := transform η;
  Cone.edge_comm x y f := eq_trans (eq_sym (naturality η f)) (comp_id_r _);
|}.

Lemma nat_cone_inv {S T: Category} {F: S ~> T} (c: Cone F): cone_nat (Cone.vertex c) (nat_cone c) = c.
Proof.
  destruct c as [c edge Hc]; simpl.
  unfold nat_cone; simpl.
  unfold cone_nat; simpl.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma cone_nat_inv {S T: Category} {F: S ~> T} (c: T) (η: Δ c ~> F): nat_cone (cone_nat c η) = η.
Proof. now natural_eq x. Qed.
