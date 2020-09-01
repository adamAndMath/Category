Require Export Base.

Structure Category := {
  obj: Type;
  hom: obj -> obj -> Type;
  id {a: obj}: hom a a;
  comp {a b c: obj}: hom b c -> hom a b -> hom a c;
  comp_assoc (a b c d: obj) (f: hom c d) (g: hom b c) (h: hom a b): comp f (comp g h) = comp (comp f g) h;
  comp_id_l (a b: obj) (f: hom a b): comp id f = f;
  comp_id_r (a b: obj) (f: hom a b): comp f id = f;
}.

Arguments comp_assoc {_ _ _ _ _} f g h.
Arguments comp_id_l {_ _ _} f.
Arguments comp_id_r {_ _ _} f.
Coercion obj: Category >-> Sortclass.

Infix "~>" := (hom _) (at level 90, right associativity): type_scope.
Infix "∘" := (comp _) (at level 40, left associativity).

Structure iso {C: Category} (X Y: C) := {
  to: X ~> Y;
  from: Y ~> X;
  from_to: from ∘ to = id C;
  to_from: to ∘ from = id C;
}.

Arguments to {C X Y} _.
Arguments from {C X Y} _.
Arguments from_to {C X Y} _.
Arguments to_from {C X Y} _.

Definition iso_refl {C: Category} (X: C): iso X X := {|
  to := id C;
  from := id C;
  from_to := comp_id_l (id C);
  to_from := comp_id_l (id C);
|}.

Definition iso_sym {C: Category} {X Y: C} (i: iso X Y): iso Y X := {|
  to := from i;
  from := to i;
  from_to := to_from i;
  to_from := from_to i;
|}.

Program Definition iso_comp {C: Category} {X Y Z: C} (i: iso Y Z) (j: iso X Y): iso X Z := {|
  to := to i ∘ to j;
  from := from j ∘ from i;
|}.
Next Obligation.
  rewrite comp_assoc.
  rewrite <- (comp_assoc (from j)).
  rewrite from_to, comp_id_r.
  apply from_to.
Qed.
Next Obligation.
  rewrite comp_assoc.
  rewrite <- (comp_assoc (to i)).
  rewrite to_from, comp_id_r.
  apply to_from.
Qed.

Definition isomorphic (C: Category) (X Y: C) := inhabited (iso X Y).

Infix "≃" := (isomorphic _) (at level 70).

Instance isomorphic_equiv C: Equivalence (isomorphic C).
Proof.
  constructor.
  + intros x.
    constructor.
    exact (iso_refl x).
  + intros x y H.
    destruct H as [i].
    constructor.
    apply iso_sym, i.
  + intros x y z H H0.
    destruct H as [i], H0 as [j].
    constructor.
    eapply iso_comp; eassumption.
Qed.

Definition eq_iso {C: Category} {X Y: C} (e: X = Y): iso X Y :=
  match e in (_ = y) return (iso X y) with
  | eq_refl => iso_refl X
  end.

Theorem eq_iso_refl {C: Category} {X: C} (e: X = X): eq_iso e = iso_refl X.
Proof.
  unfold eq_iso.
  assert (e = eq_refl).
  apply proof_irrelevance.
  subst e.
  reflexivity.
Qed.


Structure Functor (C D: Category) := {
    fobj: C -> D;
    fmap {a b: C}: (a ~> b) -> fobj a ~> fobj b;
    fmap_id {a: C}: fmap (@id _ a) = @id _ (fobj a);
    fmap_comp {a b c: C} (f: b ~> c) (g: a ~> b): fmap (f ∘ g) = fmap f ∘ fmap g;
}.

Arguments fobj {C D}.
Arguments fmap {C D} _ {a b}.
Arguments fmap_id {C D _ a}.
Arguments fmap_comp {C D _ a b c}.

Coercion fobj: Functor >-> Funclass.
Infix "~~>" := Functor (at level 90, right associativity): type_scope.

Theorem fun_eq (C D: Category) (F G: C ~~> D): F = G <-> (forall x: C, F x = G x) /\ (forall (x y: C) (f: x ~> y) (ex: F x = G x) (ey: F y = G y), to (eq_iso ey) ∘ fmap F f ∘ from (eq_iso ex) = fmap G f).
Proof.
  split.
  + intros H.
    subst G.
    split.
    intros x.
    reflexivity.
    intros x y f ex ey.
    rewrite !eq_iso_refl.
    simpl.
    rewrite comp_id_l.
    apply comp_id_r.
  + destruct F as [Fobj Fmap Fmap_id Fmap_comp], G as [Gobj Gmap Gmap_id Gmap_comp]; simpl.
    intros [Hobj Hmap].
    assert (Fobj = Gobj).
    now extensionality x.
    subst Gobj; clear Hobj.
    assert (Fmap = Gmap).
    extensionality x.
    extensionality y.
    extensionality f.
    specialize (Hmap x y f eq_refl eq_refl).
    simpl in Hmap.
    rewrite comp_id_l, comp_id_r in Hmap.
    exact Hmap.
    subst Gmap; clear Hmap.
    f_equal.
    all: apply proof_irrelevance.
Qed.

Program Definition imap {C D x y} (F: C ~~> D) (i: iso x y): iso (F x) (F y) := {|
  to := fmap F (to i);
  from := fmap F (from i);
|}.
Next Obligation.
  rewrite <- fmap_comp.
  rewrite from_to.
  apply fmap_id.
Qed.
Next Obligation.
  rewrite <- fmap_comp.
  rewrite to_from.
  apply fmap_id.
Qed.

Program Definition Cat: Category := {|
  obj := Category;
  hom := Functor;
  id C := {|
    fobj x := x;
    fmap a b f := f;
  |};
  comp A B C F G := {|
    fobj x := F (G x);
    fmap a b f := fmap F (fmap G f);
  |}
|}.
Next Obligation.
  rewrite fmap_id.
  apply fmap_id.
Qed.
Next Obligation.
  rewrite fmap_comp.
  apply fmap_comp.
Qed.
Next Obligation.
  apply fun_eq; simpl.
  rename f into F, g into G, h into H.
  split.
  now intros x.
  intros x y f ex ey.
  rewrite !eq_iso_refl.
  clear ex ey; simpl.
  rewrite comp_id_l.
  apply comp_id_r.
Qed.
Next Obligation.
  apply fun_eq; simpl.
  rename f into F.
  split.
  now intros x.
  intros x y f ex ey.
  rewrite !eq_iso_refl.
  clear ex ey; simpl.
  rewrite comp_id_l.
  apply comp_id_r.
Qed.
Next Obligation.
  apply fun_eq; simpl.
  rename f into F.
  split.
  now intros x.
  intros x y f ex ey.
  rewrite !eq_iso_refl.
  clear ex ey; simpl.
  rewrite comp_id_l.
  apply comp_id_r.
Qed.

Definition monic {C: Category} {a b: C} (f: a ~> b) :=
  forall c (g1 g2: c ~> a), f ∘ g1 = f ∘ g2 -> g1 = g2.

Definition epic {C: Category} {a b: C} (f: a ~> b) :=
  forall c (g1 g2: b ~> c), g1 ∘ f = g2 ∘ f -> g1 = g2.
