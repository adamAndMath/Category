Require Export Base.Basic.

Module Category.

Structure mixin_of@{i j} (obj: Type@{i}) := Mixin {
  hom: obj -> obj -> Type@{j};
  id (a: obj): hom a a;
  comp {a b c: obj}: hom b c -> hom a b -> hom a c;
  comp_assoc (a b c d: obj) (f: hom c d) (g: hom b c) (h: hom a b): comp f (comp g h) = comp (comp f g) h;
  comp_id_l (a b: obj) (f: hom a b): comp (id b) f = f;
  comp_id_r (a b: obj) (f: hom a b): comp f (id a) = f;
}.

Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type@{i j} := Pack { obj: Type@{i}; _: class_of@{i j} obj }.
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

Theorem cat_mixin_eq {T} (C D: Category.mixin_of T): C = D <->
  (forall x y: T, Category.hom T C x y = Category.hom T D x y) /\
  (forall (x: T) (e: Category.hom T C x x = Category.hom T D x x), match e in (_ = X) return X with eq_refl => (Category.id T C x) end = Category.id T D x) /\
  (forall (x y z: T) (f: Category.hom T C y z) (g: Category.hom T C x y) (xy: Category.hom T C x y = Category.hom T D x y) (yz: Category.hom T C y z = Category.hom T D y z) (xz: Category.hom T C x z = Category.hom T D x z),
    match xz in _ = X return X with eq_refl => Category.comp T C f g end = Category.comp T D (match yz in (_ = X) return X with eq_refl => f end) (match xy in (_ = X) return X with eq_refl => g end)
  ).
Proof.
  split.
  + intros H.
    subst D.
    repeat split.
    intros x e.
    replace e with (@eq_refl _ (Category.hom T C x x)) by apply proof_irrelevance.
    reflexivity.
    intros x y z f g xy yz xz.
    replace xy with (@eq_refl _ (Category.hom T C x y)) by apply proof_irrelevance.
    replace yz with (@eq_refl _ (Category.hom T C y z)) by apply proof_irrelevance.
    replace xz with (@eq_refl _ (Category.hom T C x z)) by apply proof_irrelevance.
    reflexivity.
  + intros [Hhom [Hid Hcomp]].
    destruct C, D.
    simpl in *.
    assert (hom0 = hom1).
    extensionality x.
    extensionality y.
    apply Hhom.
    subst hom1; clear Hhom.
    assert (id0 = id1).
    extensionality x.
    apply (Hid x eq_refl).
    subst id1; clear Hid.
    assert (comp0 = comp1).
    extensionality x.
    extensionality y.
    extensionality z.
    extensionality f.
    extensionality g.
    apply (Hcomp x y z f g eq_refl eq_refl eq_refl).
    subst comp1; clear Hcomp.
    f_equal.
    all: apply proof_irrelevance.
Qed.

Definition co_mixin@{i j} C (m: Category.mixin_of@{i j} C): Category.mixin_of@{i j} C :=
  Category.Mixin C
  (fun x y => Category.hom C m y x)
  (Category.id C m)
  (fun _ _ _ f g => Category.comp C m g f)
  (fun _ _ _ _ f g h => eq_sym (Category.comp_assoc C m _ _ _ _ h g f))
  (fun _ _ f => Category.comp_id_r C m _ _ f)
  (fun _ _ f => Category.comp_id_l C m _ _ f).

Definition co@{i j} (C: Category@{i j}): Category@{i j} :=
  Category.Pack C (co_mixin C (Category.class C)).

Lemma co_invol (C: Category): co (co C) = C.
Proof.
  destruct C.
  unfold co; simpl.
  f_equal.
  destruct m.
  unfold co_mixin; simpl.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma gen_eq_l {C: Category} {x y: C} (f g: x ~> y): f = g <-> forall (z: C) (a: y ~> z), a ∘ f = a ∘ g.
Proof.
  split; intros H.
  now subst g.
  setoid_rewrite <- comp_id_l.
  apply H.
Qed.

Lemma gen_eq_r {C: Category} {x y: C} (f g: x ~> y): f = g <-> forall (z: C) (a: z ~> x), f ∘ a = g ∘ a.
Proof.
  split; intros H.
  now subst g.
  setoid_rewrite <- comp_id_r.
  apply H.
Qed.

Lemma gen_eq {C: Category} {x y: C} (f g: x ~> y): f = g <-> forall (x' y': C) (a: x' ~> x) (b: y ~> y'), b ∘ f ∘ a = b ∘ g ∘ a.
Proof.
  split; intros H.
  now subst g.
  setoid_rewrite <- comp_id_l.
  setoid_rewrite <- comp_id_r.
  apply H.
Qed.
