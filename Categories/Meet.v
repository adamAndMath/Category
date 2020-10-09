Require Export Base.

Module Meet.

Variant obj: Set := left | right | center.

Definition hom (x y: obj) :=
  x = y \/ (x = left \/ x = right) /\ y = center.

Lemma hom_eq {x y: obj} (f g: hom x y): f = g.
Proof.
  apply proof_irrelevance.
Qed.

Lemma id (x: obj): hom x x.
Proof.
  now left.
Qed.

Lemma comp {x y z: obj}: hom y z -> hom x y -> hom x z.
Proof.
  intros [|[]] [|[]].
  all: [> left | right..].
  now transitivity y.
  all: now subst y.
Qed.

Lemma comp_assoc {a b c d: obj} (h: hom c d) (g: hom b c) (f: hom a b): comp h (comp g f) = comp (comp h g) f.
Proof. apply hom_eq. Qed.

Lemma comp_id_l {x y: obj} (f: hom x y): comp (id y) f = f.
Proof. apply hom_eq. Qed.

Lemma comp_id_r {x y: obj} (f: hom x y): comp f (id x) = f.
Proof. apply hom_eq. Qed.

Definition cat_mixin: Category.mixin_of obj :=
  Category.Mixin obj hom id (@comp) (@comp_assoc) (@comp_id_l) (@comp_id_r).

Canonical cat: Category :=
  Category.Pack obj cat_mixin.

Lemma inl: left ~> center.
Proof.
  right.
  repeat split.
  now left.
Qed.

Lemma inr: right ~> center.
Proof.
  right.
  repeat split.
  now right.
Qed.

Definition choose {A} (x y z: A) (a: obj): A :=
  match a with
  | left => x
  | right => y
  | center => z
  end.

Program Definition F {C: Category} {x y z: C} (f: x ~> z) (g: y ~> z): cat ~> C := {|
  fobj := choose x y z;
  fmap a b :=
    match a, b return hom a b -> choose x y z a ~> choose x y z b with
    | left, left => fun _ => Categories.id x
    | right, right => fun _ => Categories.id y
    | center, center => fun _ => Categories.id z
    | left, center => fun _ => f
    | right, center => fun _ => g
    | left, right => _
    | right, left => _
    | center, left => _
    | center, right => _
    end;
|}.
Next Obligation.
  contradict H.
  intros [H | [_ H]].
  all: discriminate H.
Qed.
Next Obligation.
  contradict H.
  intros [H | [_ H]].
  all: discriminate H.
Qed.
Next Obligation.
  contradict H.
  intros [H | [_ H]].
  all: discriminate H.
Qed.
Next Obligation.
  contradict H.
  intros [H | [_ H]].
  all: discriminate H.
Qed.
Next Obligation.
  now destruct a.
Qed.
Next Obligation.
  symmetry.
  destruct f0.
  subst c.
  destruct g0.
  subst b.
  destruct a.
  1, 2, 3: apply Categories.comp_id_l.
  destruct a0.
  subst b.
  destruct o.
  1, 2: subst a.
  1, 2: apply Categories.comp_id_l.
  destruct a0.
  subst c.
  destruct g0.
  subst b.
  destruct o.
  1, 2: subst a.
  1, 2: apply Categories.comp_id_r.
  destruct a0.
  subst b.
  now destruct o.
Qed.

Lemma F_unique {C: Category} (G: cat ~> C): exists (x y z: C) (f: x ~> z) (g: y ~> z), F f g = G.
Proof.
  exists (G left), (G right), (G center).
  exists (fmap G inl), (fmap G inr).
  fun_eq x y f.
  now destruct x.
  destruct x, y; simpl in *.
  all: rewrite !eq_iso_refl.
  all: clear H H0.
  all: simpl.
  all: rewrite Categories.comp_id_l, Categories.comp_id_r.
  1, 5, 9: assert (f = id _) by apply hom_eq.
  1, 2, 3: subst f.
  1, 2, 3: symmetry.
  1, 2, 3: apply (@fmap_id _ _ G).
  1, 3, 5, 6: destruct f as [H | [f H]].
  all: try discriminate H.
  all: f_equal.
  all: apply hom_eq.
Qed.

Lemma F_eq {C: Category} (F G: cat ~> C):
  F = G <->
  (forall x, F x = G x) /\
  (forall (el: F left = G left) (ec: F center = G center), eq_iso ec ∘ fmap F inl = fmap G inl ∘ eq_iso el) /\
  (forall (er: F right = G right) (ec: F center = G center), eq_iso ec ∘ fmap F inr = fmap G inr ∘ eq_iso er).
Proof.
  rewrite fun_eq.
  destruct F as [f F Fid Fcomp], G as [f' G Gid Gcomp].
  simpl.
  clear Fcomp Gcomp.
  split.
  all: intros [Hf H].
  all: split.
  1, 3: exact Hf.
  all: assert (f = f').
  1, 3: now extensionality x.
  all: subst f'; clear Hf.
  split.
  1, 2: apply H.
  intros x y g.
  destruct g.
  subst y.
  all: intros H1 H2.
  rewrite !eq_iso_refl.
  clear H1 H2.
  simpl.
  rewrite Categories.comp_id_l, Categories.comp_id_r.
  transitivity (Categories.id (f x)).
  1: rewrite <- Fid.
  2: rewrite <- Gid.
  1, 2: f_equal.
  1, 2: apply hom_eq.
  destruct a.
  subst y.
  destruct o; subst x.
  all: etransitivity.
  1, 3: etransitivity.
  2: exact (proj1 H H1 H2).
  3: exact (proj2 H H1 H2).
  all: do 2 f_equal.
  all: apply hom_eq.
Qed.

End Meet.

Canonical Meet.cat.
Notation Meet := Meet.cat.
