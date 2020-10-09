Require Export Base.

Module Two.

Definition obj := bool.
Definition hom (x y: obj) :=
  if implb x y then unit else Empty_set.

Lemma hom_eq {x y: obj} (f g: hom x y): f = g.
Proof.
  now destruct x, y, f, g.
Qed.

Definition id (x: obj): hom x x :=
  match x with
  | false => tt
  | true => tt
  end.

Definition comp {x y z: obj}: hom y z -> hom x y -> hom x z :=
  match x, y, z with
  | false, false, false => fun _ _ => tt
  | true, true, true => fun _ _ => tt
  | false, true, true => fun _ f => f
  | false, false, true => fun f _ => f
  | true, false, _ => fun _ => Empty_set_rect _
  | _, true, false => Empty_set_rect _
  end.

Lemma comp_assoc {a b c d: obj} (h: hom c d) (g: hom b c) (f: hom a b): comp h (comp g f) = comp (comp h g) f.
Proof. apply hom_eq. Qed.

Lemma comp_id_l {x y: obj} (f: hom x y): comp (id y) f = f.
Proof. apply hom_eq. Qed.

Lemma comp_id_r {x y: obj} (f: hom x y): comp f (id x) = f.
Proof. apply hom_eq. Qed.

Definition cat_mixin: Category.mixin_of obj :=
  Category.Mixin obj hom id (@comp) (@comp_assoc) (@comp_id_l) (@comp_id_r).

Definition cat: Category :=
  Category.Pack obj cat_mixin.

Program Definition F {C: Category} {x y: C} (f: x ~> y): cat ~> C := {|
  fobj b := if b then y else x;
  fmap a b :=
    match a, b return hom a b -> (if a then y else x) ~> (if b then y else x) with
    | false, false => fun _ => Categories.id x
    | true, true => fun _ => Categories.id y
    | false, true => fun _ => f
    | true, false => Empty_set_rect _
    end;
|}.
Next Obligation.
  now destruct a.
Qed.
Next Obligation.
  destruct a, b, c; simpl.
  all: try contradiction.
  all: symmetry.
  1, 2: apply Categories.comp_id_l.
  all: apply Categories.comp_id_r.
Qed.

Lemma F_unique {C: Category} (G: cat ~> C): exists (x y: C) (f: x ~> y), F f = G.
Proof.
  exists (G false), (G true), (fmap G (tt: hom false true)).
  fun_eq x y f.
  now destruct x.
  destruct x, y, f; simpl in *.
  all: rewrite !eq_iso_refl.
  all: clear H H0.
  all: simpl.
  all: rewrite Categories.comp_id_l, Categories.comp_id_r.
  1, 3: symmetry.
  1, 2: apply (@fmap_id _ _ G).
  reflexivity.
Qed.

End Two.

Notation Two := Two.cat.
Notation "2" := Two.
