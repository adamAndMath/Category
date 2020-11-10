Require Export Nat.

Module Future.
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
  | S l => step p (l + n) ∘ stepn p n l
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
  apply comm.
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

End Future.

Canonical Future.cat.
Notation Future := Future.cat.
Coercion Future.objs: Future.obj >-> Funclass.
Coercion Future.shift: Future.hom >-> Funclass.
Coercion Future.pfun: Future.obj >-> Functor.
Coercion Future.pnat: Future.hom >-> Natural.

Module Past.
Section category.
Context (C: Category).

Structure obj := Obj {
  objs: nat -> C;
  step n: objs (S n) ~> objs n;
}.

Coercion objs: obj >-> Funclass.

Structure hom (P Q: obj) := Hom {
  shift n: P n ~> Q n;
  comm n: shift n ∘ step P n = step Q n ∘ shift (S n);
}.

Coercion shift: hom >-> Funclass.

Lemma obj_eq (P Q: obj): P = Q <-> (forall n, P n = Q n) /\ (forall n (e: P n = Q n) (eS: P (S n) = Q (S n)), eq_iso e ∘ step P n = step Q n ∘ eq_iso eS).
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
  step n := step p (s + n) ∘ eq_iso (f_equal p (PeanoNat.Nat.add_succ_r s n));
|}.

Fixpoint stepn {C: Category} (p: cat C) n l: p (l + n) ~> p n :=
  match l return p (l + n) ~> p n with
  | 0 => Categories.id (p n)
  | S l => stepn p n l ∘ step p (l + n)
  end.

Program Definition pfun {C: Category} (p: obj C): Functor (co Nat) C := {|
  fobj := p;
  fmap x y f := stepn p y f ∘ (eq_iso (f_equal p (Nat.comm f)))⁻¹;
|}.
Next Obligation.
  apply Categories.comp_id_r.
Qed.
Next Obligation.
  generalize (Nat.Nat.comp_obligation_1 c b a g f).
  destruct f as [n H].
  destruct H.
  destruct g as [m H].
  destruct H.
  unfold from at 2 3; simpl.
  intros e.
  rewrite !Categories.comp_id_r.
  induction m; simpl.
  rewrite eq_iso_refl.
  reflexivity.
  injection e; intros e'.
  replace e with (f_equal S e') by apply proof_irrelevance.
  clear e.
  rewrite Categories.comp_assoc.
  rewrite <- (IHm e'); clear IHm.
  rewrite <- !Categories.comp_assoc.
  f_equal.
  destruct e'.
  unfold from; simpl.
  rewrite Categories.comp_id_l.
  apply Categories.comp_id_r.
Qed.

Program Definition pnat {C: Category} {P Q: cat C} (f: hom P Q): Natural (pfun P) (pfun Q) := {|
  transform := f;
|}.
Next Obligation.
  destruct f0 as [n H].
  destruct H.
  unfold from; simpl.
  rewrite !Categories.comp_id_r.
  induction n; simpl.
  rewrite Categories.comp_id_l.
  apply Categories.comp_id_r.
  rewrite Categories.comp_assoc.
  rewrite IHn; clear IHn.
  rewrite <- !Categories.comp_assoc.
  f_equal.
  apply comm.
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
  unfold from; simpl.
  rewrite Categories.comp_id_r.
  induction n; simpl.
  reflexivity.
  rewrite Categories.comp_id_r.
  exact IHn.
Qed.

End Past.

Canonical Past.cat.
Notation Past := Past.cat.
Coercion Past.objs: Past.obj >-> Funclass.
Coercion Past.shift: Past.hom >-> Funclass.
Coercion Past.pfun: Past.obj >-> Functor.
Coercion Past.pnat: Past.hom >-> Natural.

Section Future_iso.
Context (C: Category).

Program Definition Future_to: Future C ~> Fun Nat C := {|
  fobj p := p;
  fmap p q f := f;
|}.
Next Obligation.
  now natural_eq n.
Qed.
Next Obligation.
  now natural_eq n.
Qed.

Program Definition Future_from: Fun Nat C ~> Future C := {|
  fobj F := {|
    Future.objs := F;
    Future.step n := fmap F (Nat.step n);
  |};
  fmap F G η := {|
    Future.shift := η;
    Future.comm n := naturality η (Nat.step n);
  |}
|}.
Next Obligation.
  now apply Future.hom_eq.
Qed.
Next Obligation.
  now apply Future.hom_eq.
Qed.

Lemma Future_inv_l: Future_from ∘ Future_to = id (Future C).
Proof.
  fun_eq p q f.
  destruct x; simpl.
  f_equal.
  extensionality n.
  rewrite comp_id_r.
  apply comp_id_l.
  apply Future.hom_eq; simpl.
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

Lemma Future_inv_r: Future_to ∘ Future_from = id (Fun Nat C).
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

Canonical Future_iso: Future C <~> Fun Nat C :=
  Isomorphism.Pack Future_to (Isomorphism.Mixin _ _ _ Future_to Future_from Future_inv_l Future_inv_r).

Lemma future_as_fun: Future C ≃ Fun Nat C.
Proof.
  constructor.
  exact Future_iso.
Qed.

End Future_iso.

Section Past_iso.
Context (C: Category).

Program Definition Past_to: Past C ~> Fun (co Nat) C := {|
  fobj p := p;
  fmap p q f := f;
|}.
Next Obligation.
  now natural_eq n.
Qed.
Next Obligation.
  now natural_eq n.
Qed.

Program Definition Past_from: Fun (co Nat) C ~> Past C := {|
  fobj F := {|
    Past.objs := F;
    Past.step n := fmap F (Nat.step n);
  |};
  fmap F G η := {|
    Past.shift := η;
    Past.comm n := naturality η (Nat.step n);
  |}
|}.
Next Obligation.
  now apply Past.hom_eq.
Qed.
Next Obligation.
  now apply Past.hom_eq.
Qed.

Lemma Past_inv_l: Past_from ∘ Past_to = id (Past C).
Proof.
  fun_eq p q f.
  destruct x; simpl.
  f_equal.
  extensionality n.
  unfold from; simpl.
  rewrite comp_id_r.
  apply comp_id_l.
  apply Past.hom_eq; simpl.
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

Lemma Past_inv_r: Past_to ∘ Past_from = id (Fun (co Nat) C).
Proof.
  fun_eq F G η.
  rename x into F.
  fun_eq x y f.
  destruct f as [n H].
  destruct H; unfold from; simpl.
  rewrite comp_id_r.
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

Canonical Past_iso: Past C <~> Fun (co Nat) C :=
  Isomorphism.Pack Past_to (Isomorphism.Mixin _ _ _ Past_to Past_from Past_inv_l Past_inv_r).

Lemma past_as_fun: Past C ≃ Fun (co Nat) C.
Proof.
  constructor.
  exact Past_iso.
Qed.

End Past_iso.

Lemma CoFuture (C: Category): co (Future C) ≃ Past (co C).
Proof.
  rewrite future_as_fun, past_as_fun.
  apply coFun.
Qed.
