Require Export Structure.
Require Export Categories.Slice.

Program Definition SliceTop_mixin (C: Category) (x: C) := TopCategory.Mixin (C / x)
  {|
    Slice.dom := x;
    Slice.oarr := id x;
  |}
  (fun f => {|
    Slice.arr := Slice.oarr f;
  |})
  _.
Next Obligation.
  apply comp_id_l.
Qed.
Next Obligation.
  apply Slice.hom_eq; simpl.
  rewrite <- comp_id_l.
  symmetry.
  exact (Slice.comm f).
Qed.

Canonical SliceTop (C: Category) (x: C) := TopCategory.Pack (C / x) (SliceTop_mixin C x).

Program Definition SliceBot_mixin (C: BotCategory) (x: C) := BotCategory.Mixin (C / x)
  {|
    Slice.dom := 0;
    Slice.oarr := ¡;
  |}
  (fun f => {|
    Slice.arr := ¡;
  |})
  _.
Next Obligation.
  symmetry.
  apply from_zero_unique.
Qed.
Next Obligation.
  apply Slice.hom_eq; simpl.
  apply from_zero_unique.
Qed.

Canonical SliceBot (C: BotCategory) (x: C) := BotCategory.Pack (C / x) (SliceBot_mixin C x).

Program Definition SliceCoprod_mixin (C: CoprodCategory) (x: C) := CoprodCategory.Mixin (C / x)
  (fun f g => {|
    Slice.dom := Slice.dom f + Slice.dom g;
    Slice.oarr := [Slice.oarr f, Slice.oarr g];
  |})
  (fun f g h a b => {|
    Slice.arr := [Slice.arr a, Slice.arr b];
  |})
  (fun f g => {|
    Slice.arr := in1;
  |})
  (fun f g => {|
    Slice.arr := in2;
  |})
  _.
Next Obligation.
  rewrite merge_comp.
  f_equal; apply Slice.comm.
Qed.
Next Obligation.
  apply merge_in1.
Qed.
Next Obligation.
  apply merge_in2.
Qed.
Next Obligation.
  setoid_rewrite Slice.hom_eq; simpl.
  apply merge_in.
Qed.

Canonical SliceCoprod (C: CoprodCategory) (x: C) := CoprodCategory.Pack (C / x) (SliceCoprod_mixin C x).
