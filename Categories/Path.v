Require Export Nat.

Module Path.
Section category.
Context (C: Category).

Structure obj := Obj {
  objs: nat -> C;
  step n: objs n ~> objs (S n);
}.

Coercion objs: obj >-> Funclass.

Structure hom (P Q: obj) := Hom {
  shift n: P n ~> Q n;
  comm n: shift (S n) ∘ step P n = step Q n ∘ shift n;
}.

Coercion shift: hom >-> Funclass.

Lemma obj_eq (P Q: obj): P = Q <-> (forall n, P n = Q n) /\ (forall n (e: P n = Q n) (eS: P (S n) = Q (S n)), eq_iso eS ∘ step P n = step Q n ∘ eq_iso e).
Proof.
  split.
  + intros H.
    subst Q.
    repeat split.
    intros n e eS.
    rewrite !eq_iso_refl; clear e eS.
    simpl.
    rewrite comp_id_r.
    apply comp_id_l.
  + destruct P as [P ps], Q as [Q qs].
    simpl.
    intros [H Hs].
    apply functional_extensionality in H.
    subst Q.
    f_equal.
    extensionality n.
    specialize (Hs n eq_refl eq_refl).
    simpl in Hs.
    rewrite comp_id_l, comp_id_r in Hs.
    exact Hs.
Qed.

Lemma hom_eq {P Q: obj} (f g: hom P Q): f = g <-> forall n, f n = g n.
Proof.
  split.
  intros H.
  now subst g.
  destruct f as [f Hf], g as [g Hg].
  simpl.
  intros H.
  assert (f = g).
  now extensionality n.
  subst g; clear H.
  f_equal.
  apply proof_irrelevance.
Qed.

Program Definition id (P: obj): hom P P := {|
  shift n := id (P n);
|}.
Next Obligation.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Program Definition comp {X Y Z: obj} (f: hom Y Z) (g: hom X Y): hom X Z := {|
  shift n := f n ∘ g n;
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite comm.
  rewrite !comp_assoc.
  f_equal.
  apply comm.
Qed.

Lemma comp_assoc {a b c d: obj} (f: hom c d) (g: hom b c) (h: hom a b): comp f (comp g h) = comp (comp f g) h.
Proof.
  apply hom_eq; simpl.
  intros n.
  apply comp_assoc.
Qed.

Lemma comp_id_l {P Q: obj} (f: hom P Q): comp (id Q) f = f.
Proof.
  apply hom_eq; simpl.
  intros n.
  apply comp_id_l.
Qed.

Lemma comp_id_r {P Q: obj} (f: hom P Q): comp f (id P) = f.
Proof.
  apply hom_eq; simpl.
  intros n.
  apply comp_id_r.
Qed.

Definition cat_mixin: Category.mixin_of obj :=
  Category.Mixin obj hom id (@comp) (@comp_assoc) (@comp_id_l) (@comp_id_r).

Canonical cat: Category :=
  Category.Pack obj cat_mixin.

End category.

Arguments Obj {C} objs step.
Arguments objs {C} _ n.
Arguments step {C} _ n.
Arguments hom {C} P Q.
Arguments Hom {C P Q} shift comm.
Arguments shift {C P Q} _ n.
Arguments comm {C P Q} _ n.
Arguments obj_eq {C} P Q.
Arguments hom_eq {C P Q} f g.

Definition skip {C: Category} (s: nat) (p: cat C): cat C := {|
  objs n := p (s + n);
  step n := (eq_iso (f_equal p (PeanoNat.Nat.add_succ_r s n)))⁻¹ ∘ step p (s + n);
|}.

Fixpoint stepn {C: Category} (p: cat C) n l: p n ~> p (l + n)%nat :=
  match l return p n ~> p (l + n)%nat with
  | 0 => Categories.id (p n)
  | S l => Path.step p (l + n) ∘ stepn p n l
  end.

Program Definition pfun {C: Category} (p: obj C): Functor Nat C := {|
  fobj := p;
  fmap x y f := eq_iso (f_equal p (Nat.comm f)) ∘ stepn p x f;
|}.
Next Obligation.
  apply Categories.comp_id_l.
Qed.
Next Obligation.
  generalize (Nat.Nat.comp_obligation_1 a b c f g).
  destruct f as [n H].
  destruct H.
  destruct g as [m H].
  destruct H.
  simpl.
  intros e.
  rewrite !Categories.comp_id_l.
  induction n; simpl.
  rewrite eq_iso_refl.
  reflexivity.
  injection e; intros e'.
  replace e with (f_equal S e') by apply proof_irrelevance.
  clear e.
  rewrite <- Categories.comp_assoc.
  rewrite <- (IHn e'); clear IHn.
  rewrite !Categories.comp_assoc.
  f_equal.
  destruct e'.
  simpl.
  rewrite Categories.comp_id_r.
  apply Categories.comp_id_l.
Qed.

Program Definition pnat {C: Category} {P Q: cat C} (f: hom P Q): Natural (pfun P) (pfun Q) := {|
  transform := f;
|}.
Next Obligation.
  destruct f0 as [n H].
  destruct H.
  simpl.
  rewrite !Categories.comp_id_l.
  induction n; simpl.
  rewrite Categories.comp_id_l.
  apply Categories.comp_id_r.
  rewrite <- Categories.comp_assoc.
  rewrite <- IHn; clear IHn.
  rewrite !Categories.comp_assoc.
  f_equal.
  apply Path.comm.
Qed.

Program Definition const {C: Category}: C ~> cat C := {|
  fobj x := {|
    objs _ := x;
    step _ := Categories.id x;
  |};
  fmap x y f := {|
    shift _ := f;
  |}
|}.
Next Obligation.
  rewrite Categories.comp_id_l.
  apply Categories.comp_id_r.
Qed.
Next Obligation.
  now apply hom_eq.
Qed.
Next Obligation.
  now apply hom_eq.
Qed.

Lemma pfun_const {C: Category} (c: C): pfun (const c) = Δ c.
Proof.
  fun_eq x y f.
  destruct f as [n H].
  destruct H.
  simpl.
  rewrite Categories.comp_id_l.
  induction n; simpl.
  reflexivity.
  rewrite Categories.comp_id_l.
  exact IHn.
Qed.

End Path.

Canonical Path.cat.
Notation Path := Path.cat.
Coercion Path.objs: Path.obj >-> Funclass.
Coercion Path.shift: Path.hom >-> Funclass.
Coercion Path.pfun: Path.obj >-> Functor.
Coercion Path.pnat: Path.hom >-> Natural.

Section Path_iso.
Context (C: Category).

Program Definition Path_to: Path C ~> Fun Nat C := {|
  fobj p := p;
  fmap p q f := f;
|}.
Next Obligation.
  now natural_eq n.
Qed.
Next Obligation.
  now natural_eq n.
Qed.

Program Definition Path_from: Fun Nat C ~> Path C := {|
  fobj F := {|
    Path.objs := F;
    Path.step n := fmap F (Nat.step n);
  |};
  fmap F G η := {|
    Path.shift := η;
    Path.comm n := naturality η (Nat.step n);
  |}
|}.
Next Obligation.
  now apply Path.hom_eq.
Qed.
Next Obligation.
  now apply Path.hom_eq.
Qed.

Lemma Path_inv_l: Path_from ∘ Path_to = id (Path C).
Proof.
  fun_eq p q f.
  destruct x; simpl.
  f_equal.
  extensionality n.
  rewrite comp_id_r.
  apply comp_id_l.
  apply Path.hom_eq; simpl.
  intros n.
  transitivity (f n).
  2: symmetry.
  1: rewrite <- comp_id_l.
  2: rewrite <- comp_id_r.
  all: f_equal.
  all: apply is_eq_refl.
  1: destruct H0.
  2: destruct H.
  all: apply is_eq_id.
Qed.

Lemma Path_inv_r: Path_to ∘ Path_from = id (Fun Nat C).
Proof.
  fun_eq F G η.
  rename x into F.
  fun_eq x y f.
  destruct f as [n H].
  destruct H; simpl.
  rewrite comp_id_l.
  induction n; simpl.
  rewrite <- fmap_id.
  reflexivity.
  rewrite IHn; clear IHn.
  rewrite <- fmap_comp.
  f_equal.
  now apply Nat.hom_eq.
  natural_eq x.
  transitivity (η x).
  2: symmetry.
  1: rewrite <- comp_id_l.
  2: rewrite <- comp_id_r.
  all: f_equal.
  all: apply is_eq_refl.
  1: destruct H0.
  2: destruct H.
  all: apply is_eq_id.
Qed.

Canonical Path_iso: Path C <~> Fun Nat C :=
  Isomorphism.Pack Path_to (Isomorphism.Mixin _ _ _ Path_to Path_from Path_inv_l Path_inv_r).

Lemma path_as_fun: Path C ≃ Fun Nat C.
Proof.
  constructor.
  exact Path_iso.
Qed.

End Path_iso.
