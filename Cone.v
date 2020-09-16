Require Export Base.

Structure Cone {S T: Category} (F: S ~> T) := {
  vertex: T;
  edge x: vertex ~> F x;
  edge_comm x y (f: x ~> y): fmap F f ∘ edge x = edge y;
}.

Arguments vertex {_ _ _} _.
Arguments edge {_ _ _} _ _.
Arguments edge_comm {_ _ _} _ {_ _} _.

Structure ConeMor {S T: Category} {F: S ~> T} (N L: Cone F) := {
  mediator: vertex N ~> vertex L;
  mediator_comm x: edge L x ∘ mediator = edge N x;
}.

Arguments mediator {_ _ _ _ _} _.
Arguments mediator_comm {_ _ _ _ _} _ _.

Lemma conemor_eq {S T: Category} {F: S ~> T} {N L: Cone F} (f g: ConeMor N L): f = g <-> (mediator f = mediator g).
Proof.
  split; intros H.
  now subst g.
  destruct f as [f Hf], g as [g Hg].
  simpl in H.
  subst g.
  f_equal.
  apply proof_irrelevance.
Qed.

Ltac conemor_eq :=
  match goal with
  | [ |- ?f = ?g] =>
    apply (conemor_eq f g);
    simpl
  end.

Coercion mediator: ConeMor >-> hom.

Section Cones.
Context {S T: Category} {F: S ~> T}.

Definition cone_id (c: Cone F): ConeMor c c := {|
  mediator := id (vertex c);
  mediator_comm x := comp_id_r (edge c x);
|}.

Definition cone_comp {X Y Z: Cone F} (f: ConeMor Y Z) (g: ConeMor X Y): ConeMor X Z := {|
  mediator := f ∘ g;
  mediator_comm x := eq_trans (comp_assoc _ _ _)
    (eq_trans (f_equal2 _ (mediator_comm f x) eq_refl) (mediator_comm g x));
|}.

Lemma cone_comp_assoc (A B C D: Cone F) (f: ConeMor C D) (g: ConeMor B C) (h: ConeMor A B): cone_comp f (cone_comp g h) = cone_comp (cone_comp f g) h.
Proof.
  conemor_eq.
  apply comp_assoc.
Qed.

Lemma cone_comp_id_l (X Y: Cone F) (f: ConeMor X Y): cone_comp (cone_id Y) f = f.
Proof.
  conemor_eq.
  apply comp_id_l.
Qed.

Lemma cone_comp_id_r (X Y: Cone F) (f: ConeMor X Y): cone_comp f (cone_id X) = f.
Proof.
  conemor_eq.
  apply comp_id_r.
Qed.

End Cones.

Definition Cones_mixin {S T: Category} (F: S ~> T): Category.mixin_of (Cone F) :=
  Category.Mixin (Cone F) ConeMor cone_id (@cone_comp S T F) cone_comp_assoc cone_comp_id_l cone_comp_id_r.

Canonical Cones {S T: Category} (F: S ~> T): Category :=
  Category.Pack (Cone F) (Cones_mixin F).

Definition nat_cone {S T: Category} {F: S ~> T} (c: Cone F): Δ (vertex c) ~> F := {|
  transform := edge c: forall x, Δ (vertex c) x ~> F x;
  naturality x y f := eq_trans (comp_id_r _) (eq_sym (edge_comm c f));
|}.

Definition cone_nat {S T: Category} {F: S ~> T} (c: T) (η: Δ c ~> F): Cone F := {|
  vertex := c;
  edge := transform η;
  edge_comm x y f := eq_trans (eq_sym (naturality η f)) (comp_id_r _);
|}.

Lemma nat_cone_inv {S T: Category} {F: S ~> T} (c: Cone F): cone_nat (vertex c) (nat_cone c) = c.
Proof.
  destruct c as [c edge Hc]; simpl.
  unfold nat_cone; simpl.
  unfold cone_nat; simpl.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma cone_nat_inv {S T: Category} {F: S ~> T} (c: T) (η: Δ c ~> F): nat_cone (cone_nat c η) = η.
Proof. now natural_eq x. Qed.
