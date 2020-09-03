Require Export Structure.

Module Monad.

Structure mixin_of {C: Category} (F: Functor C C) := Mixin {
  lift: id C ~> F;
  flatten: F ∘ F ~> F;
  flatten_comm (x: C): flatten x ∘ fmap F (flatten x) = flatten x ∘ flatten (F x);
  flatten_lift_l (x: C): flatten x ∘ lift (F x) = id (F x);
  flatten_lift_r (x: C): flatten x ∘ fmap F (lift x) = id (F x);
}.

Notation class_of := mixin_of (only parsing).

Section ClassDef.
Context (C: Cat).

Structure type := Pack { functor: Functor C C; _: class_of functor }.
Local Coercion functor: type >-> Functor.

Variable (F: type).
Definition class := match F return class_of F with Pack _ c => c end.

Let Fx := (match F with Pack F _ => F end).

Definition to_obj: Fun C C := Fx.
Definition to_hom: C ~> C := Fx.

End ClassDef.

Module Exports.

Coercion functor: type >-> Functor.
Coercion to_obj: type >-> Category.obj.
Coercion to_hom: type >-> hom.
Notation Monad := type.

End Exports.

End Monad.

Export Monad.Exports.

Section Monad1.
Context {C: Category} {M: Monad C}.

Definition lift: id C ~> M := Monad.lift M (Monad.class C M).
Definition flatten: M ∘ M ~> M := Monad.flatten M (Monad.class C M).

Lemma flatten_comm (x: C): flatten x ∘ fmap M (flatten x) = flatten x ∘ flatten (M x).
Proof. apply Monad.flatten_comm. Qed.
Lemma flatten_lift_l (x: C): flatten x ∘ lift (M x) = id (M x).
Proof. apply Monad.flatten_lift_l. Qed.
Lemma flatten_lift_r (x: C): flatten x ∘ fmap M (lift x) = id (M x).
Proof. apply Monad.flatten_lift_r. Qed.

Lemma map_lift {x y: C} (f: x ~> y): fmap M f ∘ lift x = lift y ∘ f.
Proof.
  symmetry.
  apply (naturality lift).
Qed.

Lemma map_flatten {x y: C} (f: x ~> y): flatten y ∘ fmap M (fmap M f) = fmap M f ∘ flatten x.
Proof. apply (naturality flatten). Qed.

End Monad1.

Section MonoidCat.
Context {C: Category} {M: Monad C}.

Definition mon_comp {x y z: C} (f: y ~> M z) (g: x ~> M y): x ~> M z :=
  flatten z ∘ fmap M f ∘ g.

Lemma mon_comp_assoc (x y z v: C) (f: z ~> M v) (g: y ~> M z) (h: x ~> M y): mon_comp f (mon_comp g h) = mon_comp (mon_comp f g) h.
Proof.
  unfold mon_comp.
  rewrite comp_assoc.
  f_equal.
  rewrite !fmap_comp.
  rewrite !comp_assoc.
  f_equal.
  rewrite flatten_comm.
  rewrite <- !comp_assoc.
  f_equal.
  symmetry.
  apply map_flatten.
Qed.

Lemma mon_comp_id_l (x y: C) (f: x ~> M y): mon_comp (lift y) f = f.
Proof.
  unfold mon_comp.
  rewrite flatten_lift_r.
  apply comp_id_l.
Qed.

Lemma mon_comp_id_r (x y: C) (f: x ~> M y): mon_comp f (lift x) = f.
Proof.
  unfold mon_comp.
  rewrite <- comp_assoc.
  setoid_rewrite map_lift.
  rewrite comp_assoc.
  setoid_rewrite flatten_lift_l.
  apply comp_id_l.
Qed.

End MonoidCat.

Definition MCat_mixin {C: Category} (M: Monad C): Category.mixin_of C :=
  Category.Mixin C (fun x y: C => x ~> M y) lift (@mon_comp C M) mon_comp_assoc mon_comp_id_l mon_comp_id_r.

Definition MCat {C: Category} (M: Monad C): Category :=
  Category.Pack C (MCat_mixin M).