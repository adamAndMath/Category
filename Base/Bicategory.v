Require Export Base.Binatural.

Module Bicategory.

Structure mixin_of (obj: Type) := Mixin {
  bihom: obj -> obj -> Category;
  biid (x: obj): bihom x x;
  hcomp {x y z: obj}: Bifunctor (bihom y z) (bihom x y) (bihom x z);
  unitor_l {x y: obj}: fix_l hcomp (biid y) <~> id (bihom x y);
  unitor_r {x y: obj}: fix_r hcomp (biid x) <~> id (bihom x y);
  associator {x y z v: obj}: RComp (@hcomp x z v) (@hcomp x y z) <~> LComp hcomp hcomp;
  pentagon {x y z v w: obj} (f: bihom v w) (g: bihom z v) (h: bihom y z) (i: bihom x y): bmap hcomp (to associator f g h) (id i) ∘ to associator f (hcomp g h) i ∘ bmap hcomp (id f) (to associator g h i) = to associator (hcomp f g) h i ∘ to associator f g (hcomp h i);
  unit_triang {x y z: obj} (f: bihom y z) (g: bihom x y): bmap hcomp (to unitor_r f) (id g) ∘ to associator f (biid y) g = bmap hcomp (id f) (to unitor_l g)
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
Notation Bicategory := type.

End Exports.

End Bicategory.

Export Bicategory.Exports.

Definition bihom {C: Bicategory}: C -> C -> Category := Bicategory.bihom C (Bicategory.class C).
Definition biid {C: Bicategory}: forall x: C, bihom x x := Bicategory.biid C (Bicategory.class C).
Definition hcomp {C: Bicategory}: forall {x y z: C}, Bifunctor (bihom y z) (bihom x y) (bihom x z) := @Bicategory.hcomp C (Bicategory.class C).
Definition unitor_l {C: Bicategory}: forall {x y: C}, fix_l hcomp (biid y) <~> id (bihom x y) := @Bicategory.unitor_l C (Bicategory.class C).
Definition unitor_r {C: Bicategory}: forall {x y: C}, fix_r hcomp (biid x) <~> id (bihom x y) := @Bicategory.unitor_r C (Bicategory.class C).
Definition associator {C: Bicategory}: forall {x y z v: C}, RComp (@hcomp C x z v) (@hcomp C x y z) <~> LComp hcomp hcomp := @Bicategory.associator C (Bicategory.class C).

Infix "~~>" := bihom (at level 70, right associativity).
Infix "⊙" := hcomp (at level 40, left associativity).
Infix "⊚" := (bmap hcomp) (at level 40, left associativity).
Notation λ := unitor_l.
Notation ρ := unitor_r.
Notation α := associator.

Instance hcomp_iso (C: Bicategory) (x y z: C): Proper (isomorphic (y ~~> z) ==> isomorphic (x ~~> y) ==> isomorphic (x ~~> z)) hcomp.
Proof.
  intros f1 f2 Hf g1 g2 Hg.
  now apply bobj_iso.
Qed.

Section BicategoryTheory.
Context {C: Bicategory}.

Lemma pentagon: forall {x y z v w: C} (f: v ~~> w) (g: z ~~> v) (h: y ~~> z) (i: x ~~> y), to α f g h ⊚ id i ∘ to α f (g ⊙ h) i ∘ (id f ⊚ to α g h i) = to α (f ⊙ g) h i ∘ to α f g (h ⊙ i).
Proof. exact (@Bicategory.pentagon C (Bicategory.class C)). Qed.

Lemma unit_triang: forall {x y z: C} (f: y ~~> z) (g: x ~~> y), to ρ f ⊚ id g ∘ to α f (biid y) g = id f ⊚ to λ g.
Proof. exact (@Bicategory.unit_triang C (Bicategory.class C)). Qed.

Lemma hcomp_assoc {x y z v: C} (f: z ~~> v) (g: y ~~> z) (h: x ~~> y): f ⊙ (g ⊙ h) ≃ f ⊙ g ⊙ h.
Proof.
  constructor.
  exact (tritransform_iso α f g h).
Qed.

Lemma hcomp_id_l {x y: C} (f: x ~~> y): biid y ⊙ f ≃ f.
Proof.
  constructor.
  exact (transform_iso λ f).
Qed.

Lemma hcomp_id_r {x y: C} (f: x ~~> y): f ⊙ biid x ≃ f.
Proof.
  constructor.
  exact (transform_iso ρ f).
Qed.

End BicategoryTheory.

(* Hangs
Structure PseudoFunctor (S T: Bicategory) := {
  pfobj: S -> T;
  pfmap {x y: S}: Functor (x ~~> y) (pfobj x ~~> pfobj y);
  pfid (x: S): pfmap (biid x) <~> biid (pfobj x);
  pfcomp {x y z: S} (f: y ~~> z) (g: x ~~> y): pfmap (f ⊙ g) <~> pfmap f ⊙ pfmap g;
}.

Arguments pfobj {S T} _ _.
Arguments pfmap {S T} _ {_ _}.
Arguments pfid {S T} _ _.
Arguments pfcomp {S T} _ {_ _ _} _ _.
Coercion pfobj: PseudoFunctor >-> Funclass.
*)
