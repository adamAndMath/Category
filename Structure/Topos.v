Require Export Structure.FiniteCompleteClosed.
Require Export Structure.Pullback.

Module Topos.

Structure mixin_of (C: FCClosed) := Mixin {
  Subobj: C;
  truth: 1 ~> Subobj;
  sub {X Y: C} (f: X ~> Y): monic f -> Y ~> Subobj;
  sub_pullback {X Y: C} (f: X ~> Y) (Hf: monic f): is_pullback truth (sub f Hf) ! f;
  sub_unique {X Y: C} (f: X ~> Y) (g: Y ~> Subobj) (Hf: monic f): is_pullback truth g ! f -> sub f Hf = g;
}.

Section ClassDef.

Structure class_of (C: Category) := Class {
  base: FCClosed.class_of C;
  mixin: mixin_of (FCClosed.Pack C base);
}.

Local Coercion base: class_of >-> FCClosed.class_of.
Local Coercion mixin: class_of >-> mixin_of.

Structure type := Pack { sort: Category; _: class_of sort }.
Local Coercion sort: type >-> Category.

Variable (C: type).
Definition class := match C return class_of C with Pack _ c => c end.

Let xC := match C with Pack C _ => C end.
Notation xclass := (class: class_of xC).

Definition TopCategory := TopCategory.Pack C xclass.
Definition ProdCategory := ProdCategory.Pack C xclass.
Definition CartCategory := CartCategory.Pack C xclass.
Definition ExpCategory := ExpCategory.Pack C (ExpCategory.Class _ xclass xclass).
Definition CCC := CCC.Pack C xclass.
Definition EqCategory := EqCategory.Pack C xclass.
Definition FCClosed := FCClosed.Pack C xclass.

End ClassDef.

Module Exports.

Coercion base: class_of >-> FCClosed.class_of.
Coercion mixin: class_of >-> mixin_of.
Coercion sort: type >-> Category.
Coercion TopCategory: type >-> TopCategory.type.
Canonical TopCategory.
Coercion ProdCategory: type >-> ProdCategory.type.
Canonical ProdCategory.
Coercion CartCategory: type >-> CartCategory.type.
Canonical CartCategory.
Coercion ExpCategory: type >-> ExpCategory.type.
Canonical ExpCategory.
Coercion CCC: type >-> CCC.type.
Canonical CCC.
Coercion EqCategory: type >-> EqCategory.type.
Canonical EqCategory.
Coercion FCClosed: type >-> FCClosed.type.
Canonical FCClosed.
Notation Topos := type.

End Exports.

End Topos.

Export Topos.Exports.

Section ToposTheory.
Context {T: Topos}.

Definition Subobj: T := Topos.Subobj T (Topos.class T).
Definition truth: 1 ~> Subobj := Topos.truth T (Topos.class T).
Definition sub: forall {X Y: T} (f: X ~> Y), monic f -> Y ~> Subobj := @Topos.sub T (Topos.class T).

Notation Ω := Subobj.
Notation χ := sub.

Lemma sub_pullback: forall {X Y: T} (f: X ~> Y) (Hf: monic f), is_pullback truth (sub f Hf) ! f.
Proof. exact (@Topos.sub_pullback T (Topos.class T)). Qed.

Lemma sub_unique: forall {X Y: T} (f: X ~> Y) (g: Y ~> Subobj) (Hf: monic f), is_pullback truth g ! f -> sub f Hf = g.
Proof. exact (@Topos.sub_unique T (Topos.class T)). Qed.



End ToposTheory.

