Require Export Functor.

Module Bicategory.

Structure mixin_of (C: Category) := Mixin {
  hom_mixin (x y: C): Category.mixin_of (x ~> y);
  whisk_l {x y z: C} {f g: x ~> y} (h: y ~> z) (η: Category.hom (hom_mixin x y) f g): Category.hom (hom_mixin x z)
}.

(*Structure mixin_of (C: Category) := Mixin {
  hom2 {x y: C}: (x ~> y) -> (x ~> y) -> Type;
  id2 {x y: C} (f: x ~> y): hom2 f f;
  vcomp {x y: C} {f g h: x ~> y}: hom2 g h -> hom2 f g -> hom2 f h;
  whisk_l {x y z: C} {f g: x ~> y} (h: y ~> z) (η: hom2 f g): hom2 (h ∘ f) (h ∘ g);
  whisk_r {x y z: C} {g h: y ~> z} (η: hom2 g h) (f: x ~> y): hom2 (g ∘ f) (h ∘ f);
  unitor_l {x y: C} (f: x ~> y): hom2 (id y ∘ f) f;
  unitor_inv_l {x y: C} (f: x ~> y): hom2 f (id y ∘ f);
  unitor_r {x y: C} (f: x ~> y): hom2 (f ∘ id x) f;
  unitor_inv_r {x y: C} (f: x ~> y): hom2 f (f ∘ id x);
  associator {a b c d: C} (f: c ~> d) (g: b ~> c) (h: a ~> b): hom2 (f ∘ g ∘ h) (f ∘ (g ∘ h));
  associator_inv {a b c d: C} (f: c ~> d) (g: b ~> c) (h: a ~> b): hom2 (f ∘ (g ∘ h)) (f ∘ g ∘ h);
  vcomp_id_l {x y: C} (f g: x ~> y) (η: hom2 f g): vcomp (id2 g) η = η;
  vcomp_id_r {x y: C} (f g: x ~> y) (η: hom2 f g): vcomp η (id2 f) = η;
  vcomp_assoc {x y: C} (f g h i: x ~> y) (η: hom2 h i) (ϵ: hom2 g h) (μ: hom2 f g): vcomp η (vcomp ϵ μ) = vcomp (vcomp η ϵ) μ;
  whisk_id_l {a b c: C} (f: b ~> c) (g: a ~> b): whisk_l f (id2 g) = id2 (f ∘ g);
  whisk_id_r {a b c: C} (f: b ~> c) (g: a ~> b): whisk_r (id2 f) g = id2 (f ∘ g);
  whisk_comp_l {a b c: C} {g h i: a ~> b} (f: b ~> c) (η: hom2 h i) (ϵ: hom2 g h): whisk_l f (vcomp η ϵ) = vcomp (whisk_l f η) (whisk_l f ϵ);
  whisk_comp_r {a b c: C} {g h i: b ~> c} (η: hom2 h i) (ϵ: hom2 g h) (f: a ~> b): whisk_r (vcomp η ϵ) f = vcomp (whisk_r η f) (whisk_r ϵ f);
  unitor_whisk_l {a b: C} {f g: a ~> b} (η: hom2 f g): vcomp (unitor_l g) (whisk_l (id b) η) = vcomp η (unitor_l f);
  unitor_whisk_r {a b: C} {f g: a ~> b} (η: hom2 f g): vcomp (unitor_r g) (whisk_r η (id a)) = vcomp η (unitor_r f);
  associator_inv_whisk_r {a b c d: C} {h i: c ~> d} (η: hom2 h i) (f: b ~> c) (g: a ~> b): vcomp (associator_inv i f g) (whisk_r η (f ∘ g)) = vcomp (whisk_r (whisk_r η f) g) (associator_inv h f g);
  associator_inv_whisk_l {a b c d: C} {h i: a ~> b} (f: c ~> d) (g: b ~> c) (η: hom2 h i): vcomp (associator_inv f g i) (whisk_l f (whisk_l g η)) = vcomp (whisk_l (f ∘ g) η) (associator_inv f g h);
  associator_inv_whisk {a b c d: C} {h i: b ~> c} (f: c ~> d) (η: hom2 h i) (g: a ~> b): vcomp (associator_inv f i g) (whisk_l f (whisk_r η g)) = vcomp (whisk_r (whisk_l f η) g) (associator_inv f h g);
  comp_whisk {a b c: C} {f g: a ~> b} {h i: b ~> c} (η: hom2 f g) (ϵ: hom2 h i): vcomp (whisk_l i η) (whisk_r ϵ f) = vcomp (whisk_r ϵ g) (whisk_l h η);
  unitor_l_inv_l {a b: C} (f: a ~> b): vcomp (unitor_inv_l f) (unitor_l f) = id2 (id b ∘ f);
  unitor_l_inv_r {a b: C} (f: a ~> b): vcomp (unitor_l f) (unitor_inv_l f) = id2 f;
  unitor_r_inv_l {a b: C} (f: a ~> b): vcomp (unitor_inv_r f) (unitor_r f) = id2 (f ∘ id a);
  unitor_r_inv_r {a b: C} (f: a ~> b): vcomp (unitor_r f) (unitor_inv_r f) = id2 f;
  associator_inv_l {a b c d: C} (f: c ~> d) (g: b ~> c) (h: a ~> b): vcomp (associator_inv f g h) (associator f g h) = id2 (f ∘ g ∘ h);
  associator_inv_r {a b c d: C} (f: c ~> d) (g: b ~> c) (h: a ~> b): vcomp (associator f g h) (associator_inv f g h) = id2 (f ∘ (g ∘ h));
  unitor_whisk_r_to_l {a b c} :
}.*)

End Bicategory.
