Require Export Base.

Module Cone.

Section category.
Context {S T: Category} (F: Functor S T).

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

Lemma mediator_is_eq {S T: Category} {F: Functor S T} {x y: cat F} (f: x ~> y): is_eq f -> is_eq (mediator f).
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

Module Cocone.

Section category.
Context {S T: Category} (F: Functor S T).

Structure obj := Obj {
  vertex: T;
  edge x: F x ~> vertex;
  edge_comm x y (f: x ~> y): edge y ∘ fmap F f = edge x;
}.

Lemma obj_eq (N L: obj): N = L <-> vertex N = vertex L /\ (forall (x: S) (e: vertex N = vertex L), eq_iso e ∘ edge N x = edge L x).
Proof.
  split.
  + intros H.
    subst L.
    split.
    reflexivity.
    intros x e.
    rewrite eq_iso_refl.
    apply comp_id_l.
  + destruct N as [v1 e1 H1], L as [v2 e2 H2].
    simpl.
    intros [Hv He].
    subst v2.
    assert (e1 = e2).
    extensionality x.
    rewrite <- (comp_id_l (e1 x)).
    exact (He x eq_refl).
    subst e2.
    f_equal.
    apply proof_irrelevance.
Qed.

Structure hom (N L: obj) := Hom {
  mediator: vertex N ~> vertex L;
  mediator_comm x: mediator ∘ edge N x = edge L x;
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
  mediator_comm x := comp_id_l (edge c x);
|}.

Program Definition comp {X Y Z: obj} (f: hom Y Z) (g: hom X Y): hom X Z := {|
  mediator := mediator _ _ f ∘ mediator _ _ g;
  mediator_comm x := _;
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite mediator_comm.
  apply mediator_comm.
Qed.

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

Lemma mediator_is_eq {S T: Category} {F: Functor S T} {x y: cat F} (f: x ~> y): is_eq f -> is_eq (mediator f).
Proof.
  intros [e H].
  subst f y.
  simpl.
  apply is_eq_id.
Qed.

End Cocone.

Coercion Cocone.mediator: Cocone.hom >-> Categories.hom.
Canonical Cocone.cat.

Notation Cocone := Cocone.cat.

Section cocone.
Context {S T: Category} (F: Functor S T).

Program Definition cocone_to: Functor (co (Cone F)) (Cocone (cof F)) := {|
  fobj X := {|
    Cocone.vertex := Cone.vertex X;
    Cocone.edge := Cone.edge X;
    Cocone.edge_comm _ _ f := Cone.edge_comm X f;
  |};
  fmap X Y f := {|
    Cocone.mediator := Cone.mediator f;
    Cocone.mediator_comm := Cone.mediator_comm f;
  |};
|}.
Next Obligation.
  now Cocone.hom_eq.
Qed.
Next Obligation.
  now Cocone.hom_eq.
Qed.

Program Definition cocone_from: Functor (Cocone (cof F)) (co (Cone F)) := {|
  fobj X := {|
    Cone.vertex := Cocone.vertex X;
    Cone.edge := Cocone.edge X;
    Cone.edge_comm _ _ f := Cocone.edge_comm X f;
  |};
  fmap X Y f := {|
    Cone.mediator := Cocone.mediator f;
    Cone.mediator_comm := Cocone.mediator_comm f;
  |};
|}.
Next Obligation.
  now Cone.hom_eq.
Qed.
Next Obligation.
  now Cone.hom_eq.
Qed.

Lemma cocone_inv_l: cocone_from ∘ cocone_to = id (co (Cone F)).
Proof.
  fun_eq X Y f.
  now destruct x.
  destruct X as [X x Hx], Y as [Y y Hy], f as [f Hf].
  simpl in *.
  rewrite !eq_iso_refl; clear H H0.
  simpl.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Lemma cocone_inv_r: cocone_to ∘ cocone_from = id (Cocone (cof F)).
Proof.
  fun_eq X Y f.
  now destruct x.
  destruct X as [X x Hx], Y as [Y y Hy], f as [f Hf].
  simpl in *.
  rewrite !eq_iso_refl; clear H H0.
  simpl.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Canonical cocone: co (Cone F) <~> Cocone (cof F) :=
  Isomorphism.Pack cocone_to (Isomorphism.Mixin _ _ _ cocone_to cocone_from cocone_inv_l cocone_inv_r).

Lemma cone_co: co (Cone F) ≃ Cocone (cof F).
Proof.
  constructor.
  exact cocone.
Qed.

End cocone.

Definition nat_cone {S T: Category} {F: Functor S T} (c: Cone F): Δ (Cone.vertex c) ~> F := {|
  transform := Cone.edge c: forall x, Δ (Cone.vertex c) x ~> F x;
  naturality x y f := eq_trans (comp_id_r _) (eq_sym (Cone.edge_comm c f));
|}.

Definition nat_cocone {S T: Category} {F: Functor S T} (c: Cocone F): F ~> Δ (Cocone.vertex c) := {|
  transform := Cocone.edge c: forall x: S, F x ~> Δ (Cocone.vertex c) x;
  naturality x y f := eq_sym (eq_trans (comp_id_l _) (eq_sym (Cocone.edge_comm c f)));
|}.

Definition cone_nat {S T: Category} {F: Functor S T} (c: T) (η: Δ c ~> F): Cone F := {|
  Cone.vertex := c;
  Cone.edge := transform η;
  Cone.edge_comm x y f := eq_trans (eq_sym (naturality η f)) (comp_id_r _);
|}.

Definition cocone_nat {S T: Category} {F: Functor S T} (c: T) (η: F ~> Δ c): Cocone F := {|
  Cocone.vertex := c;
  Cocone.edge := transform η;
  Cocone.edge_comm x y f := eq_trans (naturality η f) (comp_id_l _);
|}.

Lemma nat_cone_inv {S T: Category} {F: Functor S T} (c: Cone F): cone_nat (Cone.vertex c) (nat_cone c) = c.
Proof.
  destruct c as [c edge Hc]; simpl.
  unfold nat_cone; simpl.
  unfold cone_nat; simpl.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma nat_cocone_inv {S T: Category} {F: Functor S T} (c: Cocone F): cocone_nat (Cocone.vertex c) (nat_cocone c: F ~> Δ (Cocone.vertex c)) = c.
Proof.
  destruct c as [c edge Hc]; simpl.
  unfold nat_cocone; simpl.
  unfold cocone_nat; simpl.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma cone_nat_inv {S T: Category} {F: Functor S T} (c: T) (η: Δ c ~> F): nat_cone (cone_nat c η) = η.
Proof. now natural_eq x. Qed.

Lemma cocone_nat_inv {S T: Category} {F: Functor S T} (c: T) (η: F ~> Δ c): nat_cocone (cocone_nat c η) = η.
Proof. now natural_eq x. Qed.

Lemma cone_iso_ex {S T: Category} {F: Functor S T} (X: Cone F) (y: T): Cone.vertex X ≃ y -> exists Y, Cone.vertex Y = y /\ X ≃ Y.
Proof.
  intros [i].
  unshelve eexists.
  exists y (fun x => Cone.edge X x ∘ i⁻¹).
  2: split.
  2: reflexivity.
  2: constructor.
  2: unshelve eexists.
  3: unshelve eexists.
  2: exists (to i).
  3: exists (to i⁻¹).
  4, 5: Cone.hom_eq.
  all: simpl.
  all: change (from i) with (to i⁻¹).
  + intros a b f.
    rewrite comp_assoc.
    f_equal.
    apply Cone.edge_comm.
  + intros a.
    rewrite <- comp_assoc, inv_l.
    apply comp_id_r.
  + now intros a.
  + apply inv_l.
  + apply inv_r.
Qed.

Lemma cocone_iso_ex {S T: Category} {F: Functor S T} (X: Cocone F) (y: T): Cocone.vertex X ≃ y -> exists Y, Cocone.vertex Y = y /\ X ≃ Y.
Proof.
  intros [i].
  unshelve eexists.
  exists y (fun x => i ∘ Cocone.edge X x).
  2: split.
  2: reflexivity.
  2: constructor.
  2: unshelve eexists.
  3: unshelve eexists.
  2: exists (to i).
  3: exists (to i⁻¹).
  4, 5: Cocone.hom_eq.
  all: simpl.
  all: change (from i) with (to i⁻¹).
  + intros a b f.
    rewrite <- comp_assoc.
    f_equal.
    apply Cocone.edge_comm.
  + now intros a.
  + intros a.
    rewrite comp_assoc, inv_l.
    apply comp_id_l.
  + apply inv_l.
  + apply inv_r.
Qed.

Program Definition cone_lift {S T: Category} (F G: Functor S T) (η: F ~> G): Cone F ~> Cone G := {|
  fobj C := {|
    Cone.vertex := Cone.vertex C;
    Cone.edge i := η i ∘ Cone.edge C i;
  |};
  fmap A B f := {|
    Cone.mediator := Cone.mediator f;
  |}
|}.
Next Obligation.
  rewrite comp_assoc.
  rewrite <- naturality.
  rewrite <- comp_assoc.
  f_equal.
  apply Cone.edge_comm.
Qed.
Next Obligation.
  rewrite <- comp_assoc.
  f_equal.
  apply Cone.mediator_comm.
Qed.
Next Obligation.
  now Cone.hom_eq.
Qed.
Next Obligation.
  now Cone.hom_eq.
Qed.

Program Definition cocone_lift {S T: Category} (F G: Functor S T) (η: F ~> G): Cocone G ~> Cocone F := {|
  fobj C := {|
    Cocone.vertex := Cocone.vertex C;
    Cocone.edge i := Cocone.edge C i ∘ η i;
  |};
  fmap A B f := {|
    Cocone.mediator := Cocone.mediator f;
  |}
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite naturality.
  rewrite comp_assoc.
  f_equal.
  apply Cocone.edge_comm.
Qed.
Next Obligation.
  rewrite comp_assoc.
  f_equal.
  apply Cocone.mediator_comm.
Qed.
Next Obligation.
  now Cocone.hom_eq.
Qed.
Next Obligation.
  now Cocone.hom_eq.
Qed.

Program Definition cone_whisk_l {A B C: Category} (F: Functor B C) (G: Functor A B): Cone G ~> Cone (F ∘ G) := {|
  fobj X := {|
    Cone.vertex := F (Cone.vertex X);
    Cone.edge i := fmap F (Cone.edge X i);
  |};
  fmap X Y f := {|
    Cone.mediator := fmap F f;
  |}
|}.
Next Obligation.
  rewrite <- fmap_comp.
  f_equal.
  apply Cone.edge_comm.
Qed.
Next Obligation.
  rewrite <- fmap_comp.
  f_equal.
  apply Cone.mediator_comm.
Qed.
Next Obligation.
  Cone.hom_eq.
  apply fmap_id.
Qed.
Next Obligation.
  Cone.hom_eq.
  apply fmap_comp.
Qed.

Program Definition cocone_whisk_l {A B C: Category} (F: Functor B C) (G: Functor A B): Cocone G ~> Cocone (F ∘ G) := {|
  fobj X := {|
    Cocone.vertex := F (Cocone.vertex X);
    Cocone.edge i := fmap F (Cocone.edge X i);
  |};
  fmap X Y f := {|
    Cocone.mediator := fmap F f;
  |}
|}.
Next Obligation.
  rewrite <- fmap_comp.
  f_equal.
  apply Cocone.edge_comm.
Qed.
Next Obligation.
  rewrite <- fmap_comp.
  f_equal.
  apply Cocone.mediator_comm.
Qed.
Next Obligation.
  Cocone.hom_eq.
  apply fmap_id.
Qed.
Next Obligation.
  Cocone.hom_eq.
  apply fmap_comp.
Qed.

Program Definition cone_whisk_r {A B C: Category} (F: Functor B C) (G: Functor A B): Cone F ~> Cone (F ∘ G) := {|
  fobj X := {|
    Cone.vertex := Cone.vertex X;
    Cone.edge i := Cone.edge X (G i);
  |};
  fmap X Y f := {|
    Cone.mediator := f;
  |}
|}.
Next Obligation.
  apply Cone.edge_comm.
Qed.
Next Obligation.
  apply Cone.mediator_comm.
Qed.
Next Obligation.
  now Cone.hom_eq.
Qed.
Next Obligation.
  now Cone.hom_eq.
Qed.

Program Definition cocone_whisk_r {A B C: Category} (F: Functor B C) (G: Functor A B): Cocone F ~> Cocone (F ∘ G) := {|
  fobj X := {|
    Cocone.vertex := Cocone.vertex X;
    Cocone.edge i := Cocone.edge X (G i);
  |};
  fmap X Y f := {|
    Cocone.mediator := f;
  |}
|}.
Next Obligation.
  apply Cocone.edge_comm.
Qed.
Next Obligation.
  apply Cocone.mediator_comm.
Qed.
Next Obligation.
  now Cocone.hom_eq.
Qed.
Next Obligation.
  now Cocone.hom_eq.
Qed.
