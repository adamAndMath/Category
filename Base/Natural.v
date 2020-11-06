Require Export Functor.

Structure Natural {C D: Category} (F G: Functor C D) := {
  transform (x: C): F x ~> G x;
  naturality {x y: C} (f: x ~> y): transform y ∘ fmap F f = fmap G f ∘ transform x;
}.

Arguments transform {_ _ _ _} _ _.
Arguments naturality {_ _ _ _} _ {_ _} _.

Coercion transform: Natural >-> Funclass.

Theorem natural_eq {C D: Category} {F G: Functor C D} (η ϵ: Natural F G): η = ϵ <-> (forall x: C, η x = ϵ x).
Proof.
  split.
  all: intro H.
  now subst ϵ.
  destruct η as [η Hη], ϵ as [ϵ Hϵ].
  simpl in H.
  assert (η = ϵ).
  now extensionality x.
  subst ϵ; clear H.
  f_equal.
  apply proof_irrelevance.
Qed.

Ltac natural_eq x :=
  match goal with
  | [ |- ?η = ?ϵ] =>
    apply (natural_eq η ϵ);
    simpl;
    intro x
  end.

Section Fun.
Context {C D: Category}.

Definition nat_id (F: C ~> D): Natural F F := {|
  transform x := id (F x);
  naturality x y f := eq_trans (comp_id_l _) (eq_sym (comp_id_r _));
|}.

Program Definition nat_comp {F G H: C ~> D} (η: Natural G H) (ϵ: Natural F G): Natural F H := {|
  transform x := η x ∘ ϵ x;
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite naturality.
  rewrite !comp_assoc.
  f_equal.
  apply naturality.
Qed.

Lemma nat_comp_assoc (F G H I: C ~> D) (η: Natural H I) (μ: Natural G H) (ϵ: Natural F G): nat_comp η (nat_comp μ ϵ) = nat_comp (nat_comp η μ) ϵ.
Proof.
  natural_eq x.
  apply comp_assoc.
Qed.

Lemma nat_comp_id_l (F G: C ~> D) (η: Natural F G): nat_comp (nat_id G) η = η.
Proof.
  natural_eq x.
  apply comp_id_l.
Qed.

Lemma nat_comp_id_r (F G: C ~> D) (η: Natural F G): nat_comp η (nat_id F) = η.
Proof.
  natural_eq x.
  apply comp_id_r.
Qed.

End Fun.

Definition Fun_mixin (C D: Category): Category.mixin_of (Functor C D) :=
  Category.Mixin (Functor C D) Natural nat_id (@nat_comp C D) nat_comp_assoc nat_comp_id_l nat_comp_id_r.

Canonical Fun (C D: Category): Category :=
  Category.Pack (Functor C D) (Fun_mixin C D).

Definition fun_hom {C D: Category} (F: Functor C D): C ~> D := F.
Coercion fun_hom: Functor >-> hom.

Definition transform_iso_mixin {C D: Category} {F G: Functor C D} (I: F <~> G) (x: C): Isomorphism.mixin_of (to I x) :=
  Isomorphism.Mixin _ _ _ (to I x) (to I⁻¹ x) ((f_equal (fun f => transform f x) (inv_l I))) ((f_equal (fun f => transform f x) (inv_r I))).

Canonical transform_iso {C D: Category} {F G: Functor C D} (I: F <~> G) (x: C): F x <~> G x :=
  Isomorphism.Pack _ (transform_iso_mixin I x).

Instance fobj_iso (C D: Category): Proper (isomorphic _ ==> isomorphic C ==> isomorphic D) fobj.
Proof.
  intros F G [I] x y [i].
  transitivity (F y).
  constructor.
  exact (imap F i).
  constructor.
  exact (transform_iso I y).
Qed.

Lemma is_iso_transform {C D: Category} {F G: C ~> D} (η: F ~> G): is_iso η <-> forall x: C, is_iso (η x).
Proof.
  split.
  + intros [ϵ [Hl Hr]] x.
    exists (ϵ x); split.
    apply (proj1 (natural_eq _ _) Hl).
    apply (proj1 (natural_eq _ _) Hr).
  + intros H.
    apply ex_forall in H.
    destruct H as [ɛ H].
    unshelve eexists.
    exists ɛ.
    2: split; natural_eq x; apply H.
    intros x y f.
    rewrite <- (comp_id_r (fmap G f)).
    rewrite <- (proj2 (H x)).
    rewrite (comp_assoc (fmap G f)).
    rewrite <- naturality.
    rewrite <- comp_assoc, comp_assoc.
    rewrite (proj1 (H y)).
    apply comp_id_l.
Qed.

Lemma transform_is_eq {C D: Category} {F G: C ~> D} (η: F ~> G) (x: C): is_eq η -> is_eq (η x).
Proof.
  intros [e H].
  subst η G.
  apply is_eq_id.
Qed.

Theorem fun_iso {C D: Category} (F G: Functor C D): F ≃ G <-> exists I: forall x: C, F x <~> G x, forall x y (f: x ~> y), I y ∘ fmap F f = fmap G f ∘ I x.
Proof.
  split.
  + intros [I].
    exists (transform_iso I).
    intros x y f.
    unfold transform_iso, inv; simpl.
    apply naturality.
  + intros [I H].
    constructor.
    unshelve eexists.
    unshelve econstructor.
    exact (fun x => I x).
    2: unshelve eexists.
    2: unshelve econstructor.
    2: exact (fun x => (I x)⁻¹).
    3, 4: natural_eq x.
    3: apply inv_l.
    3: apply inv_r.
    all: intros x y f.
    all: simpl.
    apply H.
    rewrite <- (comp_id_r _), <- (inv_r (I x)).
    rewrite comp_assoc.
    f_equal.
    rewrite <- comp_id_l, <- (inv_l (I y)).
    rewrite <- !comp_assoc.
    f_equal.
    symmetry.
    apply H.
Qed.

Lemma nat_monic {S T: Category} {F G: S ~> T} (η: F ~> G): (forall x, monic (η x)) -> monic η.
Proof.
  intros Hη Z α β H.
  natural_eq x.
  apply Hη.
  change ((η ∘ α) x = (η ∘ β) x).
  now f_equal.
Qed.

Lemma nat_epic {S T: Category} {F G: S ~> T} (η: F ~> G): (forall x, epic (η x)) -> epic η.
Proof.
  intros Hη Z α β H.
  natural_eq x.
  apply Hη.
  change ((α ∘ η) x = (β ∘ η) x).
  now f_equal.
Qed.

Lemma nat_splitmonic {S T: Category} {F G: S ~> T} (η: F ~> G): splitmonic η -> forall x, splitmonic (η x).
Proof.
  intros [ϵ H] x.
  exists (ϵ x).
  change ((ϵ ∘ η) x = id F x).
  now f_equal.
Qed.

Lemma nat_splitepic {S T: Category} {F G: S ~> T} (η: F ~> G): splitepic η -> forall x, splitepic (η x).
Proof.
  intros [ϵ H] x.
  exists (ϵ x).
  change ((η ∘ ϵ) x = id G x).
  now f_equal.
Qed.

Lemma nat_is_iso {S T: Category} {F G: S ~> T} (η: F ~> G): is_iso η <-> forall x, is_iso (η x).
Proof.
  split.
  + intros [ϵ H] x.
    exists (ϵ x); split.
    1: change ((ϵ ∘ η) x = id F x).
    2: change ((η ∘ ϵ) x = id G x).
    all: now f_equal.
  + intros H.
    apply ex_forall in H.
    destruct H as [ϵ H].
    unshelve eexists.
    exists ϵ.
    2: split.
    2, 3: natural_eq x.
    2, 3: apply H.
    intros x y f.
    rewrite <- (comp_id_r (ϵ y ∘ fmap G f)).
    rewrite <- comp_id_r.
    rewrite <- (proj2 (H x)).
    rewrite !comp_assoc.
    f_equal.
    rewrite <- !comp_assoc.
    rewrite <- naturality.
    rewrite comp_assoc.
    rewrite !(proj1 (H _)).
    rewrite comp_id_r.
    apply comp_id_l.
Qed.

Lemma ex_fobj_iso {S T: Category} (I: S <~> T) (x: T): exists x': S, to I x' = x.
Proof.
  exists (to I⁻¹ x).
  change ((I ∘ I⁻¹) x = id T x).
  f_equal.
  apply inv_r.
Qed.

Lemma ex_fmap_iso {S T: Category} {x y: S} (I: S <~> T) (f: (to I x) ~> (to I y)): exists f': x ~> y, fmap (to I) f' = f.
Proof.
  exists (to (eq_iso (inv_l I)) y ∘ fmap (to I⁻¹) f ∘ to (eq_iso (inv_l I))⁻¹ x).
  rewrite !fmap_comp.
  etransitivity.
  etransitivity.
  apply (f_equal (fun f => f ∘ _ ∘ _)).
  2: apply f_equal.
  1: apply (is_eq_unique _ (to (eq_iso (inv_r I)) (to I y))).
  3: apply (is_eq_unique _ (to (eq_iso (inv_r I))⁻¹ (to I x))).
  1, 3: apply (fmap_is_eq I).
  1: apply (transform_is_eq (eq_iso (inv_l I))).
  2: apply (transform_is_eq (eq_iso (inv_l I))⁻¹).
  3, 4: apply transform_is_eq.
  2, 4: apply is_eq_inv.
  1, 2, 3, 4: apply eq_iso_is_eq.
  setoid_rewrite (naturality (to (eq_iso (inv_r I)))).
  rewrite <- comp_assoc.
  change (f ∘ (eq_iso (inv_r I) ∘ (eq_iso (inv_r I))⁻¹) (to I x) = f).
  rewrite inv_r.
  apply comp_id_r.
Qed.

Definition whisk_l {S T U: Category} {G H: S ~> T} (F: T ~> U) (η: G ~> H): F ∘ G ~> F ∘ H := {|
  transform x := fmap F (η x): (F ∘ G) x ~> (F ∘ H) x;
  naturality x y f := eq_trans (eq_sym (fmap_comp _ _)) (eq_trans (f_equal _ (naturality _ _)) (fmap_comp _ _));
|}.

Infix "<|" := whisk_l (at level 40, no associativity).

Definition whisk_r {S T U: Category} {G H: T ~> U} (η: G ~> H) (F: S ~> T): (G ∘ F) ~> (H ∘ F) := {|
  transform x := η (F x): (G ∘ F) x ~> (H ∘ F) x;
  naturality x y f := naturality η _;
|}.

Infix "|>" := whisk_r (at level 40, no associativity).

Lemma whisk_id_l {A B C: Category} (F: B ~> C) (G: A ~> B): F <| id G = id (F ∘ G).
Proof.
  natural_eq x.
  apply fmap_id.
Qed.

Lemma whisk_id_r {A B C: Category} (F: B ~> C) (G: A ~> B): id F |> G = id (F ∘ G).
Proof. now natural_eq x. Qed.

Lemma whisk_comp_distr_l {A B C: Category} {G H I: A ~> B} (f: B ~> C) (η: H ~> I) (ϵ: G ~> H): f <| (η ∘ ϵ) = (f <| η) ∘ (f <| ϵ).
Proof.
  natural_eq x.
  apply fmap_comp.
Qed.

Lemma whisk_comp_distr_r {A B C: Category} {G H I: B ~> C} (f: A ~> B) (η: H ~> I) (ϵ: G ~> H): (η ∘ ϵ) |> f = (η |> f) ∘ (ϵ |> f).
Proof. now natural_eq x. Qed.

Lemma comp_whisk {A B C: Category} {F G: A ~> B} {H I: B ~> C} (η: F ~> G) (ϵ: H ~> I): (I <| η) ∘ (ϵ |> F) = (ϵ |> G) ∘ (H <| η).
Proof.
  natural_eq x.
  symmetry.
  apply naturality.
Qed.

Lemma is_iso_whisk_l {A B C: Category} {G H: A ~> B} (F: B ~> C) (η: G ~> H): is_iso η -> is_iso (F <| η).
Proof.
  intros [ϵ [Hl Hr]].
  exists (F <| ϵ); split.
  all: rewrite <- whisk_comp_distr_l, <- whisk_id_l.
  all: now f_equal.
Qed.

Lemma is_iso_whisk_r {A B C: Category} {G H: B ~> C} (F: A ~> B) (η: G ~> H): is_iso η -> is_iso (η |> F).
Proof.
  intros [ϵ [Hl Hr]].
  exists (ϵ |> F); split.
  all: rewrite <- whisk_comp_distr_r, <- whisk_id_r.
  all: now f_equal.
Qed.

Section whisk_iso_l.
Context {S T U: Category} {G H: S ~> T} (F: T ~> U) (η: G <~> H).

Lemma whisk_l_inv_l: F <| η⁻¹ ∘ (F <| η) = id (F ∘ G).
Proof.
  rewrite <- whisk_comp_distr_l.
  rewrite inv_l.
  apply whisk_id_l.
Qed.

Lemma whisk_l_inv_r: F <| η ∘ (F <| η⁻¹) = id (F ∘ H).
Proof.
  rewrite <- whisk_comp_distr_l.
  rewrite inv_r.
  apply whisk_id_l.
Qed.

Definition whisk_iso_l: F ∘ G <~> F ∘ H :=
  Isomorphism.Pack (F <| η) (Isomorphism.Mixin _ _ _ (F <| η) (F <| η⁻¹) whisk_l_inv_l whisk_l_inv_r).
End whisk_iso_l.

Section whisk_iso_r.
Context {S T U: Category} {G H: T ~> U} (η: G <~> H) (F: S ~> T).

Lemma whisk_r_inv_l: η⁻¹ |> F ∘ (η |> F) = id (G ∘ F).
Proof.
  rewrite <- whisk_comp_distr_r.
  rewrite inv_l.
  apply whisk_id_r.
Qed.

Lemma whisk_r_inv_r: η |> F ∘ (η⁻¹ |> F) = id (H ∘ F).
Proof.
  rewrite <- whisk_comp_distr_r.
  rewrite inv_r.
  apply whisk_id_r.
Qed.

Definition whisk_iso_r: G ∘ F <~> H ∘ F :=
  Isomorphism.Pack (η |> F) (Isomorphism.Mixin _ _ _ (η |> F) (η⁻¹ |> F) whisk_r_inv_l whisk_r_inv_r).
End whisk_iso_r.

Infix "<||" := whisk_iso_l (at level 40, no associativity).
Infix "||>" := whisk_iso_r (at level 40, no associativity).

Program Definition unitor_l {S T: Category} (F: S ~> T): id T ∘ F <~> F :=
  Isomorphism.Pack _ (Isomorphism.Mixin _ _ _ {|
  transform x := id (F x);
  naturality x y f := eq_trans (comp_id_l (fmap F f)) (eq_sym (comp_id_r (fmap F f)));
|} {|
  transform x := id (F x);
  naturality x y f := eq_trans (comp_id_l (fmap F f)) (eq_sym (comp_id_r (fmap F f)));
|} _ _).
Next Obligation.
  natural_eq x.
  apply comp_id_l.
Qed.
Next Obligation.
  natural_eq x.
  apply comp_id_l.
Qed.

Program Definition unitor_r {S T: Category} (F: S ~> T): F ∘ id S <~> F :=
  Isomorphism.Pack _ (Isomorphism.Mixin _ _ _ {|
  transform x := id (F x);
  naturality x y f := eq_trans (comp_id_l (fmap F f)) (eq_sym (comp_id_r (fmap F f)));
|} {|
  transform x := id (F x);
  naturality x y f := eq_trans (comp_id_l (fmap F f)) (eq_sym (comp_id_r (fmap F f)));
|} _ _).
Next Obligation.
  natural_eq x.
  apply comp_id_l.
Qed.
Next Obligation.
  natural_eq x.
  apply comp_id_l.
Qed.

Program Definition associator {A B C D: Category} (F: C ~> D) (G: B ~> C) (H: A ~> B): F ∘ (G ∘ H) <~> F ∘ G ∘ H :=
  Isomorphism.Pack _ (Isomorphism.Mixin _ _ _ {|
  transform x := id (F (G (H x)));
  naturality x y f := eq_trans (comp_id_l _) (eq_sym (comp_id_r _));
|} {|
  transform x := id (F (G (H x)));
  naturality x y f := eq_trans (comp_id_l _) (eq_sym (comp_id_r _));
|} _ _).
Next Obligation.
  natural_eq x.
  apply comp_id_l.
Qed.
Next Obligation.
  natural_eq x.
  apply comp_id_l.
Qed.

Notation λ := unitor_l.
Notation ρ := unitor_r.
Notation α := associator.

Lemma unitor_l_is_eq {S T: Category} (F: S ~> T): is_eq (λ F).
Proof.
  exists (comp_id_l F).
  natural_eq x.
  symmetry.
  apply is_eq_refl.
  apply (transform_is_eq (eq_iso (comp_id_l F))).
  apply eq_iso_is_eq.
Qed.

Lemma unitor_r_is_eq {S T: Category} (F: S ~> T): is_eq (ρ F).
Proof.
  exists (comp_id_r F).
  natural_eq x.
  symmetry.
  apply is_eq_refl.
  apply (transform_is_eq (eq_iso (comp_id_r F))).
  apply eq_iso_is_eq.
Qed.

Lemma associator_is_eq {A B C D: Category} (F: C ~> D) (G: B ~> C) (H: A ~> B): is_eq (α F G H).
Proof.
  exists (comp_assoc F G H).
  natural_eq x.
  symmetry.
  apply is_eq_refl.
  apply (transform_is_eq (eq_iso (comp_assoc F G H))).
  apply eq_iso_is_eq.
Qed.

Lemma unitor_whisk_l {S T: Category} {F G: S ~> T} (η: F ~> G): λ G ∘ (id T <| η) = η ∘ λ F.
Proof.
  natural_eq x.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Lemma unitor_whisk_r {S T: Category} {F G: S ~> T} (η: F ~> G): ρ G ∘ (η |> id S) = η ∘ ρ F.
Proof.
  natural_eq x.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Lemma assoc_whisk_r {A B C D: Category} {H I: C ~> D} (η: H ~> I) (F: B ~> C) (G: A ~> B): α I F G ∘ (η |> (F ∘ G)) = ((η |> F) |> G) ∘ α H F G.
Proof.
  natural_eq x.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Lemma assoc_whisk_l {A B C D: Category} {H I: A ~> B} (F: C ~> D) (G: B ~> C) (η: H ~> I): α F G I ∘ (F <| (G <| η)) = ((F ∘ G) <| η) ∘ α F G H.
Proof.
  natural_eq x.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Lemma assoc_whisk {A B C D: Category} {H I: B ~> C} (F: C ~> D) (η: H ~> I) (G: A ~> B): α F I G ∘ (F <| (η |> G)) = ((F <| η) |> G) ∘ α F H G.
Proof.
  natural_eq x.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Lemma assoc_unitor_r {A B C: Category} (F: B ~> C) (G: A ~> B): (ρ F |> G) ∘ α F (id B) G = F <| λ G.
Proof.
  natural_eq x.
  rewrite fmap_id.
  apply comp_id_l.
Qed.

Program Definition hcomp {S T U: Category} {F G: S ~> T} {J K: T ~> U} (ϵ: J ~> K) (η: F ~> G): (J ∘ F) ~> (K ∘ G) := 
  (ϵ |> G) ∘ (J <| η).

Infix "○" := hcomp (at level 40, left associativity).

Lemma hcomp_alt {S T U: Category} {F G: S ~> T} {J K: T ~> U} (ϵ: J ~> K) (η: F ~> G):
  ϵ ○ η = (K <| η) ∘ (ϵ |> F).
Proof.
  symmetry.
  apply comp_whisk.
Qed.

Lemma is_eq_whisk_l {A B C: Category} {G H: A ~> B} (F: B ~> C) (η: G ~> H): is_eq η -> is_eq (F <| η).
Proof.
  intros [H0 H1].
  subst η H.
  simpl.
  rewrite whisk_id_l.
  apply is_eq_id.
Qed.

Lemma is_eq_whisk_r {A B C: Category} {G H: B ~> C} (η: G ~> H) (F: A ~> B): is_eq η -> is_eq (η |> F).
Proof.
  intros [H0 H1].
  subst η H.
  simpl.
  rewrite whisk_id_r.
  apply is_eq_id.
Qed.

Lemma eq_iso_whisk_l {A B C: Category} {F G: A ~> B} {H I: B ~> C} (e: F ~> G) (η: H ~> I): is_eq e -> (I <| e) ∘ (η |> F) = η |> G ∘ (H <| e).
Proof.
  intros [H1 He1].
  subst e G.
  simpl.
  rewrite !whisk_id_l.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Lemma eq_iso_whisk_r {A B C: Category} {F G: A ~> B} {H I: B ~> C} (η: F ~> G) (e: H ~> I): is_eq e -> (e |> G) ∘ (H <| η) = (I <| η) ∘ (e |> F).
Proof.
  intros [H1 He1].
  subst e I.
  simpl.
  rewrite !whisk_id_r.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Lemma eq_iso_whisk_l2 {A B C D: Category} {F: B ~> C} {G: A ~> B} {H: A ~> C} {I J: C ~> D} (e: F ∘ G ~> H) (η: I ~> J): is_eq e -> (J <| e) ∘ (α J F G)⁻¹ ∘ ((η |> F) |> G) = (η |> H) ∘ (I <| e) ∘ (α I F G)⁻¹.
Proof.
  intros [H1 He1].
  subst e.
  subst H.
  simpl.
  change (from ?i) with (to i⁻¹).
  rewrite !whisk_id_l.
  rewrite comp_id_r, comp_id_l.
  rewrite <- (comp_id_r (_ |> _)).
  rewrite <- (inv_r (α I F G)).
  rewrite (comp_assoc (_ |> _)).
  rewrite (comp_assoc (α J F G)⁻¹).
  f_equal.
  rewrite <- assoc_whisk_r.
  rewrite (comp_assoc (α J F G)⁻¹).
  rewrite inv_l.
  apply comp_id_l.
Qed.

Program Definition diagonal {T S: Category}: T ~> Fun S T := {|
  fobj c := {|
    fobj _ := c;
    fmap _ _ _ := id c;
    fmap_id _ := eq_refl;
    fmap_comp _ _ _ _ _ := eq_sym (comp_id_l (id c));
  |};
  fmap x y f := {|
    transform _ := f;
    naturality _ _ _ := eq_trans (comp_id_r f) (eq_sym (comp_id_l f));
  |};
  fmap_id _ := _;
  fmap_comp _ _ _ _ _ := _;
|}.
Next Obligation.
  now natural_eq x.
Qed.
Next Obligation.
  now natural_eq x.
Qed.

Notation Δ := diagonal.

Lemma diag_comp {A B C: Category} (c: C) (F: A ~> B): Δ c ∘ F = Δ c.
Proof. now fun_eq x y f. Qed.

Lemma comp_diag {A B C: Category} (F: B ~> C) (c: B): F ∘ @Δ B A c = Δ (F c).
Proof.
  fun_eq x y f.
  apply fmap_id.
Qed.

Lemma cof_diag_c {S T: Category} (c: T): cof (@Δ T S c) = Δ (c: co T).
Proof.
  fun_eq x y f.
  now rewrite !eq_iso_refl.
Qed.

Lemma cof'_diag_c {S T: Category} (c: T): cof' (@Δ (co T) (co S) c) = Δ c.
Proof.
  now fun_eq x y f.
Qed.

Program Definition Hom: co Cat ~> Fun Cat Cat := {|
  fobj S := {|
    fobj T := Fun S T;
    fmap C D F := {|
      fobj G := F ∘ G;
      fmap _ _ η := F <| η;
      fmap_id G := whisk_id_l F G;
      fmap_comp _ _ _ ϵ η := whisk_comp_distr_l F ϵ η;
    |};
  |};
  fmap A B F := {|
    transform T := {|
      fobj G := F ∘ G;
      fmap _ _ η := η |> F;
      fmap_id G := whisk_id_r G F;
      fmap_comp _ _ _ ϵ η := whisk_comp_distr_r F ϵ η;
    |};
  |}
|}.
Next Obligation.
  fun_eq F G η.
  exact (comp_id_l x).
  rewrite (is_eq_unique_iso (eq_iso H) (λ F)).
  rewrite (is_eq_unique_iso (eq_iso H0) (λ G)).
  apply unitor_whisk_l.
  1, 3: apply eq_iso_is_eq.
  all: apply unitor_l_is_eq.
Qed.
Next Obligation.
  fun_eq F G η.
  symmetry.
  apply (comp_assoc f).
  rewrite (is_eq_unique_iso (eq_iso H) (α f g F)⁻¹).
  rewrite (is_eq_unique_iso (eq_iso H0) (α f g G)⁻¹).
  apply (iso_monic (α _ _ _)).
  rewrite !comp_assoc, inv_r, comp_id_l.
  apply (iso_epic (α _ _ _)).
  rewrite <- comp_assoc, inv_l, comp_id_r.
  symmetry.
  apply assoc_whisk_l.
  1, 3: apply eq_iso_is_eq.
  all: apply is_eq_inv.
  all: apply associator_is_eq.
Qed.
Next Obligation.
  fun_eq G H η.
  symmetry.
  apply (comp_assoc f x0 F).
  rewrite (is_eq_unique_iso (eq_iso H0) (α f G F)⁻¹).
  rewrite (is_eq_unique_iso (eq_iso H1) (α f H F)⁻¹).
  apply (iso_monic (α _ _ _)).
  rewrite !comp_assoc, inv_r, comp_id_l.
  apply (iso_epic (α _ _ _)).
  rewrite <- comp_assoc, inv_l, comp_id_r.
  symmetry.
  apply assoc_whisk.
  1, 3: apply eq_iso_is_eq.
  all: apply is_eq_inv.
  all: apply associator_is_eq.
Qed.
Next Obligation.
  natural_eq b.
  fun_eq F G η.
  apply (comp_id_r x).
  rewrite (is_eq_unique_iso (eq_iso H) (ρ F)).
  rewrite (is_eq_unique_iso (eq_iso H0) (ρ G)).
  apply unitor_whisk_r.
  1, 3: apply eq_iso_is_eq.
  all: apply unitor_r_is_eq.
Qed.
Next Obligation.
  natural_eq X.
  fun_eq F G η.
  apply (comp_assoc x g f).
  rewrite (is_eq_unique_iso (eq_iso H) (α F g f)).
  rewrite (is_eq_unique_iso (eq_iso H0) (α G g f)).
  apply assoc_whisk_r.
  1, 3: apply eq_iso_is_eq.
  all: apply associator_is_eq.
Qed.

Definition Comp_l {A B C: Category} (F: B ~> C): Fun A B ~> Fun A C := {|
  fobj G := F ∘ G;
  fmap _ _ η := F <| η;
  fmap_id G := whisk_id_l F G;
  fmap_comp _ _ _ ϵ η := whisk_comp_distr_l F ϵ η;
|}.

Definition Comp_r {A B C: Category} (G: A ~> B): Fun B C ~> Fun A C := {|
  fobj (F: B ~> C) := F ∘ G;
  fmap _ _ η := η |> G;
  fmap_id F := whisk_id_r F G;
  fmap_comp _ _ _ ϵ η := whisk_comp_distr_r G ϵ η;
|}.

Section Comp_l_iso.
Context {A B C: Category} {I: B <~> C}.

Lemma Comp_l_inv_l: Comp_l I⁻¹ ∘ Comp_l I = id (Fun A B).
Proof.
  fun_eq F G η.
  rewrite comp_assoc, from_to.
  apply (comp_id_l x).
  change (from I) with (to I⁻¹) in *.
  rewrite (is_eq_unique (eq_iso H) (λ F ∘ (eq_iso (inv_l I) |> F) ∘ α I⁻¹ I F)).
  rewrite (is_eq_unique (eq_iso H0) (λ G ∘ (eq_iso (inv_l I) |> G) ∘ α I⁻¹ I G)).
  rewrite comp_assoc, (comp_assoc η).
  rewrite <- comp_assoc.
  rewrite assoc_whisk_l.
  rewrite (comp_assoc _ (_ <| η)).
  f_equal.
  rewrite <- (comp_assoc (λ G)).
  rewrite eq_iso_whisk_r.
  rewrite comp_assoc.
  f_equal.
  apply unitor_whisk_l.
  1, 2, 4: apply eq_iso_is_eq.
  all: repeat apply is_eq_comp.
  1, 4: apply associator_is_eq.
  2, 4: apply unitor_l_is_eq.
  all: apply is_eq_whisk_r.
  all: apply eq_iso_is_eq.
Qed.

Lemma Comp_l_inv_r: Comp_l I ∘ Comp_l I⁻¹ = id (Fun A C).
Proof.
  fun_eq F G η.
  rewrite comp_assoc, to_from.
  apply (comp_id_l x).
  change (from I) with (to I⁻¹) in *.
  rewrite (is_eq_unique (eq_iso H) (λ F ∘ (eq_iso (inv_r I) |> F) ∘ α I I⁻¹ F)).
  rewrite (is_eq_unique (eq_iso H0) (λ G ∘ (eq_iso (inv_r I) |> G) ∘ α I I⁻¹ G)).
  rewrite comp_assoc, (comp_assoc η).
  rewrite <- comp_assoc.
  rewrite assoc_whisk_l.
  rewrite (comp_assoc _ (_ <| η)).
  f_equal.
  rewrite <- (comp_assoc (λ G)).
  rewrite eq_iso_whisk_r.
  rewrite comp_assoc.
  f_equal.
  apply unitor_whisk_l.
  1, 2, 4: apply eq_iso_is_eq.
  all: repeat apply is_eq_comp.
  1, 4: apply associator_is_eq.
  2, 4: apply unitor_l_is_eq.
  all: apply is_eq_whisk_r.
  all: apply eq_iso_is_eq.
Qed.

End Comp_l_iso.

Definition Comp_l_iso_mixin {A B C: Category} (I: B <~> C): Isomorphism.mixin_of (@Comp_l A B C I) :=
  Isomorphism.Mixin Cat (Fun A B) (Fun A C) (Comp_l I) (Comp_l I⁻¹) Comp_l_inv_l Comp_l_inv_r.

Definition Comp_l_iso {A B C: Category} (I: B <~> C): Fun A B <~> Fun A C :=
  Isomorphism.Pack (Comp_l I) (Comp_l_iso_mixin I).

Section Comp_r_iso.
Context {A B C: Category} {I: A <~> B}.

Lemma Comp_r_inv_l: Comp_r I⁻¹ ∘ Comp_r I = id (Fun B C).
Proof.
  fun_eq F G η.
  rewrite <- comp_assoc, to_from.
  apply (comp_id_r x).
  change (from I) with (to I⁻¹) in *.
  rewrite (is_eq_unique (eq_iso H) (ρ F ∘ (F <| eq_iso (inv_r I)) ∘ (α F I I⁻¹)⁻¹)).
  rewrite (is_eq_unique (eq_iso H0) (ρ G ∘ (G <| eq_iso (inv_r I)) ∘ (α G I I⁻¹)⁻¹)).
  rewrite comp_assoc, (comp_assoc η).
  apply (iso_epic (α _ _ _)).
  rewrite <- comp_assoc.
  rewrite <- assoc_whisk_r.
  rewrite (comp_assoc _ (α _ _ _)).
  rewrite <- !(comp_assoc _ (α _ _ _)⁻¹), !inv_l, !comp_id_r.
  rewrite <- comp_assoc.
  rewrite eq_iso_whisk_l.
  rewrite (comp_assoc (ρ G)).
  f_equal.
  apply unitor_whisk_r.
  1, 2, 4: apply eq_iso_is_eq.
  all: repeat apply is_eq_comp.
  1, 4: apply is_eq_inv, associator_is_eq.
  2, 4: apply unitor_r_is_eq.
  all: apply is_eq_whisk_l.
  all: apply eq_iso_is_eq.
Qed.

Lemma Comp_r_inv_r: Comp_r I ∘ Comp_r I⁻¹ = id (Fun A C).
Proof.
  fun_eq F G η.
  rewrite <- comp_assoc, from_to.
  apply (comp_id_r x).
  change (from I) with (to I⁻¹) in *.
  rewrite (is_eq_unique (eq_iso H) (ρ F ∘ (F <| eq_iso (inv_l I)) ∘ (α F I⁻¹ I)⁻¹)).
  rewrite (is_eq_unique (eq_iso H0) (ρ G ∘ (G <| eq_iso (inv_l I)) ∘ (α G I⁻¹ I)⁻¹)).
  rewrite comp_assoc, (comp_assoc η).
  apply (iso_epic (α _ _ _)).
  rewrite <- comp_assoc.
  rewrite <- assoc_whisk_r.
  rewrite (comp_assoc _ (α _ _ _)).
  rewrite <- !(comp_assoc _ (α _ _ _)⁻¹), !(inv_l (α _ _ _)), !comp_id_r.
  rewrite <- comp_assoc.
  rewrite eq_iso_whisk_l.
  rewrite (comp_assoc (ρ G)).
  f_equal.
  apply unitor_whisk_r.
  1, 2, 4: apply eq_iso_is_eq.
  all: repeat apply is_eq_comp.
  1, 4: apply is_eq_inv, associator_is_eq.
  2, 4: apply unitor_r_is_eq.
  all: apply is_eq_whisk_l.
  all: apply eq_iso_is_eq.
Qed.

End Comp_r_iso.

Definition Comp_r_iso_mixin {A B C: Category} (I: A <~> B): Isomorphism.mixin_of (@Comp_r A B C I) :=
  Isomorphism.Mixin Cat (Fun B C) (Fun A C) (Comp_r I) (Comp_r I⁻¹) Comp_r_inv_l Comp_r_inv_r.

Definition Comp_r_iso {A B C: Category} (I: A <~> B): Fun B C <~> Fun A C :=
  Isomorphism.Pack (Comp_r I) (Comp_r_iso_mixin I).

Instance Fun_iso: Proper (isomorphic Cat ==> isomorphic Cat ==> isomorphic Cat) Fun.
Proof.
  intros S S' I T T' J.
  transitivity (Fun S' T).
  1: clear T' J; destruct I as [I].
  2: clear S I; rename S' into S; destruct J as [I].
  all: constructor.
  apply Comp_r_iso, inv, I.
  apply Comp_l_iso, I.
Qed.

Instance Comp_iso (A B C: Category): Proper (isomorphic (Fun B C) ==> isomorphic (Fun A B) ==> isomorphic (Fun A C)) comp.
Proof.
  intros F F' HF G G' HG.
  transitivity (F' ∘ G).
  1: clear G' HG; destruct HF as [η].
  2: clear F HF; rename F' into F; destruct HG as [η].
  all: constructor.
  exact (imap (Comp_r G) η).
  exact (imap (Comp_l F) η).
Qed.

Section CoFun.
Context (S T: Category).

Program Definition CoFun_to: co (Fun S T) ~> Fun (co S) (co T) := {|
  fobj F := cof F;
  fmap F G η := {|
    transform x := η x;
  |};
|}.
Next Obligation.
  symmetry.
  apply (naturality η).
Qed.
Next Obligation.
  now natural_eq x.
Qed.
Next Obligation.
  now natural_eq x.
Qed.

Program Definition CoFun_from: Fun (co S) (co T) ~> co (Fun S T) := {|
  fobj F := cof' F;
  fmap F G η := {|
    transform x := η x;
  |};
|}.
Next Obligation.
  symmetry.
  apply (naturality η).
Qed.
Next Obligation.
  now natural_eq x.
Qed.
Next Obligation.
  now natural_eq x.
Qed.

Lemma CoFun_inv_l: CoFun_from ∘ CoFun_to = id (co (Fun S T)).
Proof.
  fun_eq F G η.
  apply cof_inv_l.
  natural_eq x.
  etransitivity.
  etransitivity.
  apply f_equal.
  3: apply (f_equal (fun f => f ∘ _)).
  3: symmetry.
  1, 3: apply is_eq_refl.
  1: destruct H0.
  2: destruct H.
  1, 2: apply is_eq_id.
  rewrite comp_id_l.
  apply comp_id_r.
Qed.

Lemma CoFun_inv_r: CoFun_to ∘ CoFun_from = id (Fun (co S) (co T)).
Proof.
  fun_eq F G η.
  apply cof_inv_r.
  natural_eq x.
  etransitivity.
  etransitivity.
  apply (f_equal (fun f => f ∘ _)).
  3: apply f_equal.
  3: symmetry.
  1, 3: apply is_eq_refl.
  1: destruct H0.
  2: destruct H.
  1, 2: apply is_eq_id.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Definition CoFun: co (Fun S T) <~> Fun (co S) (co T) :=
  Isomorphism.Pack CoFun_to (Isomorphism.Mixin _ _ _ CoFun_to CoFun_from CoFun_inv_l CoFun_inv_r).

Lemma coFun: co (Fun S T) ≃ Fun (co S) (co T).
Proof.
  constructor.
  exact CoFun.
Qed.
End CoFun.

Lemma cof_diag (S T: Category): cof (@Δ T S) ≃ (CoFun S T)⁻¹ ∘ @Δ (co T) (co S).
Proof.
  apply fun_iso.
  unshelve eexists.
  intros x.
  simpl in x.
  unfold comp, Category.comp, Cat, Category.class, Cat_mixin, fun_comp.
  unfold fobj at 2.
  simpl to.
  unfold CoFun, from, Isomorphism.inv, Isomorphism.class.
  unfold CoFun_from.
  unfold fobj at 2.
  unshelve eexists.
  eexists (fun _ => id x).
  easy.
  unshelve eexists.
  eexists (fun _ => id x).
  easy.
  1, 2: natural_eq y.
  1, 2: apply comp_id_l.
  intros x y f.
  natural_eq a.
  rewrite comp_id_l.
  apply comp_id_r.
Qed.

Lemma iso_full {S T: Category} (F: S <~> T): full F.
Proof.
  intros x y f.
  exists (to (eq_iso (inv_l F)) y ∘ fmap (to F⁻¹) f ∘ to (eq_iso (inv_l F))⁻¹ x).
  rewrite !fmap_comp.
  etransitivity.
  etransitivity.
  1: apply (f_equal (fun f => f ∘ _ ∘ _)).
  2: apply f_equal.
  1: apply (is_eq_unique _ (to (eq_iso (inv_r F)) (to F y))).
  3: apply (is_eq_unique _ (to (eq_iso (inv_r F))⁻¹ (to F x))).
  1, 3: apply (fmap_is_eq F).
  1: apply (transform_is_eq (eq_iso (inv_l F))).
  2: apply (transform_is_eq (eq_iso (inv_l F))⁻¹).
  3, 4: apply transform_is_eq.
  2, 4: apply is_eq_inv.
  1, 2, 3, 4: apply eq_iso_is_eq.
  etransitivity.
  apply (f_equal (fun f => f ∘ _)).
  apply (naturality (to (eq_iso (inv_r F)))).
  rewrite <- comp_assoc, <- comp_id_r.
  f_equal.
  apply (inv_r (transform_iso (eq_iso (inv_r F)) (to F x))).
Qed.

Lemma iso_faithful {S T: Category} (F: S <~> T): faithful F.
Proof.
  intros x y f g H.
  change (fmap (id S) f = fmap (id S) g).
  apply (iso_epic (transform_iso (eq_iso (inv_l F)) x)).
  simpl to.
  rewrite <- !naturality.
  simpl.
  now do 2 f_equal.
Qed.

Lemma iso_fully_faithful {S T: Category} (F: S <~> T): fully_faithful F.
Proof.
  apply full_and_faithful.
  split.
  apply iso_full.
  apply iso_faithful.
Qed.

Lemma iso_esurj {S T: Category} (F: S <~> T): esurj F.
Proof.
  intros x.
  exists (to F⁻¹ x).
  constructor.
  exact (transform_iso (eq_iso (inv_r F)) x).
Qed.

Instance full_natural_iso (S T: Category): Proper (isomorphic (Fun S T) ==> iff) full.
Proof.
  enough (Proper (isomorphic (Fun S T) ==> impl) full).
  now split; apply H.
  intros F F' [I] HF x y f.
  specialize (HF x y (to I⁻¹ y ∘ f ∘ to I x)).
  destruct HF as [f' H].
  apply (f_equal (fun f => transform_iso I y ∘ f ∘ transform_iso I⁻¹ x)) in H.
  rewrite !comp_assoc in H.
  rewrite inv_r, comp_id_l in H.
  rewrite <- (comp_assoc f) in H.
  setoid_rewrite (inv_r (transform_iso I x)) in H.
  rewrite comp_id_r in H.
  subst f.
  exists f'.
  simpl.
  rewrite naturality.
  rewrite <- comp_assoc.
  setoid_rewrite (inv_r (transform_iso I x)).
  symmetry.
  apply comp_id_r.
Qed.

Instance faithful_natural_iso (S T: Category): Proper (isomorphic (Fun S T) ==> iff) faithful.
Proof.
  enough (Proper (isomorphic (Fun S T) ==> impl) faithful).
  now split; apply H.
  intros F F' [I] HF x y f g H.
  apply HF; clear HF.
  apply (iso_monic (transform_iso I y)).
  simpl.
  rewrite !naturality.
  now f_equal.
Qed.

Instance fully_faithful_natural_iso (S T: Category): Proper (isomorphic (Fun S T) ==> iff) fully_faithful.
Proof.
  intros F G H.
  rewrite !full_and_faithful.
  now do 2 f_equiv.
Qed.

Instance esurj_natural_iso (S T: Category): Proper (isomorphic (Fun S T) ==> iff) esurj.
Proof.
  enough (Proper (isomorphic (Fun S T) ==> impl) esurj).
  now split; apply H.
  intros F G H HF y.
  specialize (HF y).
  destruct HF as [x HF].
  exists x.
  now rewrite <- H.
Qed.

Lemma natural_monic {S T: Category} {F G: S ~> T} (η: F ~> G): (forall x, monic (η x)) -> monic η.
Proof.
  intros Hη X α β H.
  generalize (proj1 (natural_eq _ _) H).
  clear H; intros H.
  natural_eq x.
  apply Hη, H.
Qed.

Lemma natural_epic {S T: Category} {F G: S ~> T} (η: F ~> G): (forall x, epic (η x)) -> epic η.
Proof.
  intros Hη X α β H.
  generalize (proj1 (natural_eq _ _) H).
  clear H; intros H.
  natural_eq x.
  apply Hη, H.
Qed.

Lemma transform_splitmonic {S T: Category} {F G: S ~> T} (η: F ~> G): splitmonic η -> (forall x, splitmonic (η x)).
Proof.
  intros [η' Hη] x.
  generalize (proj1 (natural_eq _ _) Hη).
  clear Hη; intros Hη.
  exists (η' x).
  apply Hη.
Qed.

Lemma transform_splitepic {S T: Category} {F G: S ~> T} (η: F ~> G): splitepic η -> (forall x, splitepic (η x)).
Proof.
  intros [η' Hη] x.
  generalize (proj1 (natural_eq _ _) Hη).
  clear Hη; intros Hη.
  exists (η' x).
  apply Hη.
Qed.
