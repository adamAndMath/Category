Require Export Base.

Module Category.

Structure mixin_of (obj: Type) := Mixin {
  hom: obj -> obj -> Type;
  id (a: obj): hom a a;
  comp {a b c: obj}: hom b c -> hom a b -> hom a c;
  comp_assoc (a b c d: obj) (f: hom c d) (g: hom b c) (h: hom a b): comp f (comp g h) = comp (comp f g) h;
  comp_id_l (a b: obj) (f: hom a b): comp (id b) f = f;
  comp_id_r (a b: obj) (f: hom a b): comp f (id a) = f;
}.

Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type := Pack { obj: Type; _: class_of obj }.
Local Coercion obj: type >-> Sortclass.

Variable (C: type).
Definition class := match C return class_of C with Pack _ c => c end.

End ClassDef.

Module Exports.

Coercion obj: type >-> Sortclass.
Notation Category := type.

End Exports.

End Category.

Export Category.Exports.

Section Category1.
Context {C: Category}.

Definition hom: C -> C -> Type := Category.hom C (Category.class C).
Definition id: forall a: C, hom a a := Category.id C (Category.class C).
Definition comp: forall {a b c: C}, hom b c -> hom a b -> hom a c := @Category.comp C (Category.class C).
Lemma comp_assoc {a b c d: C} (f: hom c d) (g: hom b c) (h: hom a b): comp f (comp g h) = comp (comp f g) h.
Proof. apply Category.comp_assoc. Qed.
Lemma comp_id_l {a b: C} (f: hom a b): comp (id b) f = f.
Proof. apply Category.comp_id_l. Qed.
Lemma comp_id_r {a b: C} (f: hom a b): comp f (id a) = f.
Proof. apply Category.comp_id_r. Qed.

End Category1.

Infix "~>" := hom (at level 70, right associativity).
Infix "∘" := comp (at level 40, left associativity).

Module Isomorphism.

Structure mixin_of {C: Category} {x y: C} (f: x ~> y) := Mixin {
  inv: y ~> x;
  inv_l: inv ∘ f = id x;
  inv_r: f ∘ inv = id y;
}.

Notation class_of := mixin_of (only parsing).

Section ClassDef.
Context {C: Category} {x y: C}.

Structure type := Pack { morphism: x ~> y; _: class_of morphism }.
Local Coercion morphism: type >-> hom.

Variable (i: type).
Definition class := match i return class_of i with Pack _ c => c end.

End ClassDef.

Module Exports.

Arguments type {_} _ _.
Coercion morphism: type >-> hom.
Notation iso := type.

End Exports.

End Isomorphism.

Export Isomorphism.Exports.

Section iso.
Context {C: Category} {x y: C} (i: iso x y).

Definition inv: y ~> x := Isomorphism.inv i (Isomorphism.class i).

Lemma inv_l: inv ∘ i = id x.
Proof. apply Isomorphism.inv_l. Qed.
Lemma inv_r: i ∘ inv = id y.
Proof. apply Isomorphism.inv_r. Qed.

Definition inv_iso_mixin: Isomorphism.mixin_of inv :=
  Isomorphism.Mixin _ _ _ inv i inv_r inv_l.

Global Canonical inv_iso: iso y x :=
  Isomorphism.Pack inv inv_iso_mixin.

End iso.

Notation "i '⁻¹'" := (inv i) (at level 9).

Definition id_iso_mixin {C: Category} (x: C): Isomorphism.mixin_of (id x) :=
  Isomorphism.Mixin C x x (id x) (id x) (comp_id_l (id x)) (comp_id_l (id x)).

Canonical id_iso {C: Category} (x: C): iso x x :=
  Isomorphism.Pack (id x) (id_iso_mixin x).

Section Comp_iso.
Context {C: Category} {x y z: C} (i: iso y z) (j: iso x y).

Lemma comp_inv_l: j⁻¹ ∘ i⁻¹ ∘ (i ∘ j) = id x.
Proof.
  rewrite comp_assoc.
  rewrite <- (comp_assoc (j⁻¹)).
  rewrite inv_l, comp_id_r.
  apply inv_l.
Qed.

Lemma comp_inv_r: i ∘ j ∘ (j⁻¹ ∘ i⁻¹) = id z.
Proof.
  rewrite comp_assoc.
  rewrite <- (comp_assoc i).
  rewrite inv_r, comp_id_r.
  apply inv_r.
Qed.

Definition iso_comp_mixin: Isomorphism.mixin_of (i ∘ j) :=
  Isomorphism.Mixin _ _ _ (i ∘ j) (j⁻¹ ∘ i⁻¹) comp_inv_l comp_inv_r.

Global Canonical iso_comp: iso x z :=
  Isomorphism.Pack (i ∘ j) iso_comp_mixin.

End Comp_iso.

Definition isomorphic (C: Category) (X Y: C) := inhabited (iso X Y).

Infix "≃" := (isomorphic _) (at level 70).

Instance isomorphic_equiv C: Equivalence (isomorphic C).
Proof.
  constructor.
  + intros x.
    constructor.
    exact (id_iso x).
  + intros x y H.
    destruct H as [i].
    constructor.
    exact (inv_iso i).
  + intros x y z H H0.
    destruct H as [i], H0 as [j].
    constructor.
    eapply iso_comp; eassumption.
Qed.

Definition eq_iso {C: Category} {X Y: C} (e: X = Y): iso X Y :=
  match e in (_ = y) return (iso X y) with
  | eq_refl => id_iso X
  end.

Theorem eq_iso_refl {C: Category} {X: C} (e: X = X): eq_iso e = id_iso X.
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

Theorem fun_eq {C D: Category} (F G: Functor C D): F = G <-> (forall x: C, F x = G x) /\ (forall (x y: C) (f: x ~> y) (ex: F x = G x) (ey: F y = G y), eq_iso ey ∘ fmap F f ∘ (eq_iso ex)⁻¹ = fmap G f).
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
    unfold inv in Hmap; simpl in Hmap.
    rewrite comp_id_l, comp_id_r in Hmap.
    exact Hmap.
    subst Gmap; clear Hmap.
    f_equal.
    all: apply proof_irrelevance.
Qed.

Ltac fun_eq :=
  match goal with
  | [ |- ?F = ?G] =>
    apply (fun_eq F G); simpl;
    split; [
      intro;
      reflexivity
    | let x := fresh in
      let y := fresh in
      let f := fresh in
      let ex := fresh in
      let ey := fresh in
      intros x y f ex ey;
      try (
        rewrite (eq_iso_refl ex), (eq_iso_refl ey);
        etransitivity; [ apply comp_id_r | ];
        etransitivity; [ apply comp_id_l | ];
        clear ex ey
      );
      try ()
    ]
  end.

Section Cat.

Definition fun_id (C: Category): Functor C C := {|
  fobj x := x;
  fmap a b f := f;
  fmap_id a := eq_refl;
  fmap_comp _ _ _ f g := eq_refl;
|}.

Definition fun_comp {C D E: Category} (F: Functor D E) (G: Functor C D): Functor C E := {|
  fobj x := F (G x);
  fmap a b f := fmap F (fmap G f);
  fmap_id a := eq_trans (f_equal _ (fmap_id)) fmap_id;
  fmap_comp _ _ _ f g := eq_trans (f_equal _ (fmap_comp f g)) (fmap_comp (fmap G f) (fmap G g));
|}.

Lemma fun_comp_assoc (A B C D: Category) (F: Functor C D) (G: Functor B C) (H: Functor A B): fun_comp F (fun_comp G H) = fun_comp (fun_comp F G) H.
Proof. now fun_eq. Qed.

Lemma fun_comp_id_l (A B: Category) (F: Functor A B): fun_comp (fun_id B) F = F.
Proof. now fun_eq. Qed.

Lemma fun_comp_id_r (A B: Category) (F: Functor A B): fun_comp F (fun_id A) = F.
Proof. now fun_eq. Qed.

Definition Cat_mixin: Category.mixin_of Category :=
  Category.Mixin Category Functor fun_id (@fun_comp) fun_comp_assoc fun_comp_id_l fun_comp_id_r.

Global Canonical Cat: Category :=
  Category.Pack Category Cat_mixin.

End Cat.

Section fmap_iso.
Context {C D: Category} {x y: C} (F: C ~> D) (i: iso x y).

Lemma fmap_inv_l: fmap F i⁻¹ ∘ fmap F i = id (F x).
Proof.
  rewrite <- fmap_comp.
  rewrite inv_l.
  apply fmap_id.
Qed.

Lemma fmap_inv_r: fmap F i ∘ fmap F i⁻¹ = id (F y).
Proof.
  rewrite <- fmap_comp.
  rewrite inv_r.
  apply fmap_id.
Qed.

Definition fmap_iso_mixin: Isomorphism.mixin_of (fmap F i) :=
  Isomorphism.Mixin _ _ _ (fmap F i) (fmap F i⁻¹) fmap_inv_l fmap_inv_r.

Global Canonical fmap_iso: iso (F x) (F y) :=
  Isomorphism.Pack (fmap F i) fmap_iso_mixin.

End fmap_iso.

Structure Natural {C D: Category} (F G: Functor C D) := {
  transform (x: C): F x ~> G x;
  naturality {x y: C} (f: x ~> y): transform y ∘ fmap F f = fmap G f ∘ transform x;
}.

Arguments transform {_ _ _ _} _ _.
Arguments naturality {_ _ _ _} _ {_ _} _.

Coercion transform: Natural >-> Funclass.

Theorem natural_eq {C D: Category} {F G: Functor C D} (η ϵ: Natural F G): η = ϵ <-> (forall x: C, η x = ϵ x).
Proof.
  split.
  all: intro H.
  now subst ϵ.
  destruct η as [η Hη], ϵ as [ϵ Hϵ].
  simpl in H.
  assert (η = ϵ).
  now extensionality x.
  subst ϵ; clear H.
  f_equal.
  apply proof_irrelevance.
Qed.

Ltac natural_eq x :=
  match goal with
  | [ |- ?η = ?ϵ] =>
    apply (natural_eq η ϵ);
    simpl;
    intro x
  end.

Section Fun.
Context {C D: Category}.

Definition nat_id (F: C ~> D): Natural F F := {|
  transform x := id (F x);
  naturality x y f := eq_trans (comp_id_l _) (eq_sym (comp_id_r _));
|}.

Program Definition nat_comp {F G H: C ~> D} (η: Natural G H) (ϵ: Natural F G): Natural F H := {|
  transform x := η x ∘ ϵ x;
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite naturality.
  rewrite !comp_assoc.
  f_equal.
  apply naturality.
Qed.

Lemma nat_comp_assoc (F G H I: C ~> D) (η: Natural H I) (μ: Natural G H) (ϵ: Natural F G): nat_comp η (nat_comp μ ϵ) = nat_comp (nat_comp η μ) ϵ.
Proof.
  natural_eq x.
  apply comp_assoc.
Qed.

Lemma nat_comp_id_l (F G: C ~> D) (η: Natural F G): nat_comp (nat_id G) η = η.
Proof.
  natural_eq x.
  apply comp_id_l.
Qed.

Lemma nat_comp_id_r (F G: C ~> D) (η: Natural F G): nat_comp η (nat_id F) = η.
Proof.
  natural_eq x.
  apply comp_id_r.
Qed.

End Fun.

Definition Fun_mixin (C D: Category): Category.mixin_of (Functor C D) :=
  Category.Mixin (Functor C D) Natural nat_id (@nat_comp C D) nat_comp_assoc nat_comp_id_l nat_comp_id_r.

Canonical Fun (C D: Category): Category :=
  Category.Pack (Functor C D) (Fun_mixin C D).

Definition fun_hom {C D: Category} (F: Functor C D): C ~> D := F.
Coercion fun_hom: Functor >-> hom.

Definition monic {C: Category} {a b: C} (f: a ~> b) :=
  forall c (g1 g2: c ~> a), f ∘ g1 = f ∘ g2 -> g1 = g2.

Definition epic {C: Category} {a b: C} (f: a ~> b) :=
  forall c (g1 g2: b ~> c), g1 ∘ f = g2 ∘ f -> g1 = g2.
