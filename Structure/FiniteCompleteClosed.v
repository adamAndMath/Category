Require Export Structure.CartisianClosed.
Require Export Structure.Equalizer.

Module FCClosed.

Section ClassDef.

Structure class_of (C: Category) := Class {
  base: CCC.class_of C;
  mixin: EqCategory.mixin_of C;
}.
Local Coercion base: class_of >-> CCC.class_of.
Local Coercion mixin: class_of >-> EqCategory.mixin_of.

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

End ClassDef.

Module Exports.

Coercion base: class_of >-> CCC.class_of.
Coercion mixin: class_of >-> EqCategory.mixin_of.
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
Notation FCClosed := type.

End Exports.

End FCClosed.

Export FCClosed.Exports.

Section FiniteCompleteClosed.
Context {C: FCClosed}.

End FiniteCompleteClosed.
