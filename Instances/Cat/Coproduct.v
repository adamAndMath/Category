Require Export Structure.

Section CoprodCategory.
Context {C D: Category}.

Definition CoprodMor (x y: C + D): Type :=
  match x, y with
  | inl x, inl y => x ~> y
  | inr x, inr y => x ~> y
  | inl _, inr _
  | inr _, inl _ => Empty_set
  end.

Definition Coprod_id (x: C + D): CoprodMor x x :=
  match x with
  | inl x => id x
  | inr x => id x
  end.

Definition Coprod_comp {x y z: C + D}: CoprodMor y z -> CoprodMor x y -> CoprodMor x z :=
  match x, y, z return CoprodMor y z -> CoprodMor x y -> CoprodMor x z with
  | inl x, inl y, inl z => comp
  | inr x, inr y, inr z => comp
  | inl _, inr _, _ => fun _ => Empty_set_rect _
  | inr _, inl _, _ => fun _ => Empty_set_rect _
  | inl _, inl _, inr _ => Empty_set_rect _
  | inr _, inr _, inl _ => Empty_set_rect _
  end.

Lemma Coprod_comp_assoc (a b c d: C + D) (f: CoprodMor c d) (g: CoprodMor b c) (h: CoprodMor a b): Coprod_comp f (Coprod_comp g h) = Coprod_comp (Coprod_comp f g) h.
Proof.
  destruct a as [a | a], b as [b | b].
  2, 3: destruct h.
  all: destruct c as [c | c].
  2, 3: destruct g.
  all: destruct d as [d | d].
  2, 3: destruct f.
  all: apply comp_assoc.
Qed.

Lemma Coprod_comp_id_l (x y: C + D) (f: CoprodMor x y): Coprod_comp (Coprod_id y) f = f.
Proof.
  destruct x as [x | x], y as [y | y].
  2, 3: destruct f.
  all: apply comp_id_l.
Qed.

Lemma Coprod_comp_id_r (x y: C + D) (f: CoprodMor x y): Coprod_comp f (Coprod_id x) = f.
Proof.
  destruct x as [x | x], y as [y | y].
  2, 3: destruct f.
  all: apply comp_id_r.
Qed.

End CoprodCategory.

Definition Coprod_mixin (C D: Category): Category.mixin_of (C + D) :=
  Category.Mixin (C + D) CoprodMor Coprod_id (@Coprod_comp C D)
  Coprod_comp_assoc Coprod_comp_id_l Coprod_comp_id_r.

Canonical Coprod (C D: Category): Category :=
  Category.Pack (C + D) (Coprod_mixin C D).

Definition Merge {C D E: Category} (F: C ~> E) (G: D ~> E): Coprod C D ~> E := {|
  fobj x :=
    match x with
    | inl x => F x
    | inr x => G x
    end;
  fmap x y :=
    match x, y with
    | inl x, inl y => fmap F
    | inr x, inr y => fmap G
    | inl _, inr _ => Empty_set_rect _
    | inr _, inl _ => Empty_set_rect _
    end;
  fmap_id x :=
    match x with
    | inl x => fmap_id
    | inr x => fmap_id
    end;
  fmap_comp x y z :=
    match x, y, z with
    | inl x, inl y, inl z => @fmap_comp _ _ F x y z
    | inr x, inr y, inr z => @fmap_comp _ _ G x y z
    | inl _, inr _, _ => fun _ => Empty_set_rect _
    | inr _, inl _, _ => fun _ => Empty_set_rect _
    | inl _, inl _, inr _ => Empty_set_rect _
    | inr _, inr _, inl _ => Empty_set_rect _
    end;
|}.

Definition Inl {C D: Category}: C ~> Coprod C D := {|
  fobj := inl;
  fmap _ _ f := f;
  fmap_id x := eq_refl;
  fmap_comp _ _ _ f g := eq_refl;
|}.

Definition Inr {C D: Category}: D ~> Coprod C D := {|
  fobj := inr;
  fmap _ _ f := f;
  fmap_id x := eq_refl;
  fmap_comp _ _ _ f g := eq_refl;
|}.

Lemma Merge_InlInr {C D E: Category} (F: C ~> E) (G: D ~> E) (H: Coprod C D ~> E): H = Merge F G <-> H ∘ Inl = F /\ H ∘ Inr = G.
Proof.
  split.
  + intros ?.
    subst H.
    split.
    1, 2: now fun_eq x y f.
  + intros [? ?].
    subst F G.
    rename H into F.
    symmetry.
    fun_eq x y f.
    now destruct x.
    destruct x as [x | x], y as [y | y].
    2, 3: destruct f.
    all: rewrite !eq_iso_refl.
    all: unfold inv; simpl.
    all: rewrite comp_id_r.
    all: apply comp_id_l.
Qed.

Definition CatCoprod_mixin: CoprodCategory.mixin_of Cat :=
  CoprodCategory.Mixin Cat Coprod (@Merge) (@Inl) (@Inr) (@Merge_InlInr).

Canonical CatCoprod: CoprodCategory :=
  CoprodCategory.Pack Cat CatCoprod_mixin.
