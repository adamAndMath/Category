Require Export Base.

Module Parallel.

Definition obj: Set := bool.

Definition hom (a b: obj): Set :=
  match a, b with
  | false, false
  | true, true => unit
  | false, true => bool
  | true, false => Empty_set
  end.

Definition id (a: obj): hom a a :=
  match a with
  | false
  | true => tt
  end.

Definition comp {a b c: obj}: hom b c -> hom a b -> hom a c :=
  match a, b, c with
  | false, false, false => fun _ _ => tt
  | true, true, true => fun _ _ => tt
  | false, false, true => fun f _ => f
  | false, true, true => fun _ f => f
  | true, false, _ => fun _ => Empty_set_rect _
  | _, true, false => Empty_set_rect _
  end.

Lemma comp_assoc (a b c d: bool) (f: hom c d) (g: hom b c) (h: hom a b): comp f (comp g h) = comp (comp f g) h.
Proof.
  destruct a, b, c, d.
  all: try contradiction.
  all: reflexivity.
Qed.

Lemma comp_id_l (x y: bool) (f: hom x y): comp (id y) f = f.
Proof.
  destruct x, y.
  2: contradiction.
  all: simpl in *.
  1, 3: now destruct f.
  reflexivity.
Qed.

Lemma comp_id_r (x y: bool) (f: hom x y): comp f (id x) = f.
Proof.
  destruct x, y.
  2: contradiction.
  all: simpl in *.
  1, 3: now destruct f.
  reflexivity.
Qed.

Definition cat_mixin: Category.mixin_of bool :=
  Category.Mixin bool hom id (@comp)
  comp_assoc comp_id_l comp_id_r.

Definition cat: Category :=
  Category.Pack bool cat_mixin.

Definition arr (a: bool): @Categories.hom cat false true := a.

Program Definition dual_to: cat ~> co cat := {|
  fobj := negb: cat -> co cat;
  fmap a b :=
    match a, b return @Categories.hom cat a b -> @Categories.hom (co cat) (negb a) (negb b) with
    | false, false => fun f => f
    | true, true => fun f => f
    | false, true => fun f => f
    | true, false => fun f => f
    end;
|}.
Next Obligation.
  now destruct a.
Qed.
Next Obligation.
  red in f, g; simpl in f, g; red in f, g.
  destruct a, b, c; simpl.
  all: try contradiction.
  all: reflexivity.
Qed.

Program Definition dual_from: co cat ~> cat := {|
  fobj := negb: co cat -> cat;
  fmap a b :=
    match a, b return @Categories.hom (co cat) a b -> @Categories.hom cat (negb a) (negb b) with
    | false, false => fun f => f
    | true, true => fun f => f
    | false, true => fun f => f
    | true, false => fun f => f
    end;
|}.
Next Obligation.
  now destruct a.
Qed.
Next Obligation.
  red in f, g; simpl in f, g; red in f, g.
  destruct a, b, c; simpl.
  all: try contradiction.
  all: reflexivity.
Qed.

Lemma dual_inv_l: dual_from ∘ dual_to = Categories.id cat.
Proof.
  fun_eq a b f.
  apply Bool.negb_involutive.
  destruct a, b, f.
  all: simpl in *.
  all: rewrite !eq_iso_refl; clear H H0.
  all: reflexivity.
Qed.

Lemma dual_inv_r: dual_to ∘ dual_from = Categories.id (co cat).
Proof.
  fun_eq a b f.
  apply Bool.negb_involutive.
  destruct a, b, f.
  all: simpl in *.
  all: rewrite !eq_iso_refl; clear H H0.
  all: reflexivity.
Qed.

Definition dual_mixin: Isomorphism.mixin_of dual_to :=
  Isomorphism.Mixin Cat cat (co cat) dual_to dual_from dual_inv_l dual_inv_r.

Definition dual: cat <~> co cat :=
  Isomorphism.Pack dual_to dual_mixin.

End Parallel.

Notation Parallel := Parallel.cat.
