Require Export Categories.Typ.

Module Discrete.
Section category.
Context (T: Type).

Let obj := T.
Let hom := @eq obj.

Lemma hom_eq {x y: T} (f g: hom x y): f = g.
Proof.
  apply proof_irrelevance.
Qed.

Let id (x: T): hom x x := eq_refl.
Let comp {x y z: T} (f: hom y z) (g: hom x y): hom x z := eq_trans g f.

Lemma comp_assoc {a b c d: T} (f: hom c d) (g: hom b c) (h: hom a b): comp f (comp g h) = comp (comp f g) h.
Proof. apply hom_eq. Qed.

Lemma comp_id_l {x y: T} (f: hom x y): comp (id y) f = f.
Proof. apply hom_eq. Qed.

Lemma comp_id_r {x y: T} (f: hom x y): comp f (id x) = f.
Proof. apply hom_eq. Qed.

Definition cat_mixin: Category.mixin_of obj :=
  Category.Mixin obj hom id (@comp) (@comp_assoc) (@comp_id_l) (@comp_id_r).

Definition cat := Category.Pack obj cat_mixin.

End category.

Program Definition func {T} {C: Category} (f: T -> C) := {|
  fobj (x: cat T) := f x;
  fmap x y e := eq_iso (f_equal f e);
|}.
Next Obligation.
  apply is_eq_unique, is_eq_comp.
  all: apply eq_iso_is_eq.
Qed.

Lemma func_fobj {T} {C: Category} (F: Functor (cat T) C): func F = F.
Proof.
  fun_eq x y H.
  destruct H; simpl.
  symmetry.
  apply (@fmap_id _ _ F x).
Qed.

Lemma func_surj {T} {C: Category} (F: Functor (cat T) C): exists f, func f = F.
Proof.
  exists F.
  apply func_fobj.
Qed.

End Discrete.

Notation Discrete := Discrete.cat.

Program Definition disc: Typ ~> Cat := {|
  fobj := Discrete;
  fmap A B f := {|
    fobj := f;
    fmap := f_equal f;
    fmap_id _ := eq_refl;
    fmap_comp _ _ _ _ _ := Discrete.hom_eq _ _ _;
  |};
|}.
Next Obligation.
  fun_eq x y f.
  apply Discrete.hom_eq.
Qed.
Next Obligation.
  fun_eq x y h.
  apply Discrete.hom_eq.
Qed.

Definition forget: Cat ~> Typ := {|
  fobj := Category.obj;
  fmap := @fobj;
  fmap_id _ := eq_refl;
  fmap_comp _ _ _ _ _ := eq_refl;
|}.

Program Definition disc_unit: disc ∘ forget ~> id Cat := {|
  transform C := {|
    fobj x := x;
    fmap x y e := eq_iso e;
  |};
|}.
Next Obligation.
  apply is_eq_unique.
  2: apply is_eq_comp.
  all: apply eq_iso_is_eq.
Qed.
Next Obligation.
  rename x into C, y into D, f into F.
  fun_eq x y f.
  destruct f.
  symmetry.
  apply fmap_id.
Qed.

Program Definition disc_counit: id Typ ~> forget ∘ disc := {|
  transform T x := x;
|}.

Lemma disc_adj_by: adjoint_by disc forget disc_unit disc_counit.
Proof.
  apply adjoint_by_alt.
  split.
  intros T.
  fun_eq x y f.
  apply Discrete.hom_eq.
  intros C.
  extensionality x.
  reflexivity.
Qed.

Lemma disc_adj: disc -| forget.
Proof.
  exists disc_unit, disc_counit.
  apply disc_adj_by.
Qed.
