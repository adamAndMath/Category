Require Export Base.

Module Nat.
Section category.
Let obj := nat.

Structure hom (n m: nat) := Hom {
  diff: nat;
  comm: diff + n = m;
}.

Coercion diff: hom >-> nat.

Lemma hom_eq {n m} (f g: hom n m): f = g <-> diff _ _ f = g.
Proof.
  split.
  intros H.
  now subst g.
  destruct f as [f Hf], g as [g Hg].
  simpl.
  intros H.
  subst g.
  f_equal.
  apply proof_irrelevance.
Qed.

Definition id n: hom n n := {|
  diff := 0;
  comm := eq_refl;
|}.

Program Definition comp {x y z} (f: hom y z) (g: hom x y): hom x z := {|
  diff := f + g;
|}.
Next Obligation.
  rewrite <- PeanoNat.Nat.add_assoc.
  rewrite comm.
  apply comm.
Qed.

Lemma comp_assoc {a b c d} (f: hom c d) (g: hom b c) (h: hom a b): comp f (comp g h) = comp (comp f g) h.
Proof.
  apply hom_eq; simpl.
  apply PeanoNat.Nat.add_assoc.
Qed.

Lemma comp_id_l {n m} (f: hom n m): comp (id m) f = f.
Proof. now apply hom_eq. Qed.

Lemma comp_id_r {n m} (f: hom n m): comp f (id n) = f.
Proof.
  apply hom_eq; simpl.
  apply PeanoNat.Nat.add_0_r.
Qed.

Definition cat_mixin: Category.mixin_of obj :=
  Category.Mixin obj hom id (@comp) (@comp_assoc) (@comp_id_l) (@comp_id_r).

Canonical cat: Category :=
  Category.Pack obj cat_mixin.

End category.

Arguments Hom {n m} diff comm.
Arguments diff {n m} _.
Arguments comm {n m} _.

Program Definition Step: cat ~> cat := {|
  fobj n := S n;
  fmap n m f := {|
    diff := f;
  |};
|}.
Next Obligation.
  rewrite PeanoNat.Nat.add_succ_r.
  f_equal.
  apply comm.
Qed.
Next Obligation.
  now apply hom_eq.
Qed.
Next Obligation.
  now apply hom_eq.
Qed.

Program Definition step: Categories.id cat ~> Step := {|
  transform n := {|
    diff := 1;
    comm := eq_refl;
  |};
|}.
Next Obligation.
  apply hom_eq; simpl.
  rewrite PeanoNat.Nat.add_comm.
  reflexivity.
Qed.

End Nat.

Canonical Nat.cat.
Notation Nat := Nat.cat.
Coercion Nat.diff: Nat.hom >-> nat.
