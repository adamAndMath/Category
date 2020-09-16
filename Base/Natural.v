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

Definition unitor_l {S T: Category} (F: S ~> T): id T ∘ F <~> F := eq_iso (comp_id_l F).
Definition unitor_r {S T: Category} (F: S ~> T): F ∘ id S <~> F := eq_iso (comp_id_r F).
Definition associator {A B C D: Category} (F: C ~> D) (G: B ~> C) (H: A ~> B): F ∘ (G ∘ H) <~> F ∘ G ∘ H := eq_iso (comp_assoc F G H).

Notation λ := unitor_l.
Notation ρ := unitor_r.
Notation α := associator.

Lemma unitor_l_is_eq {S T: Category} (F: S ~> T): is_eq (λ F).
Proof. apply eq_iso_is_eq. Qed.

Lemma unitor_r_is_eq {S T: Category} (F: S ~> T): is_eq (ρ F).
Proof. apply eq_iso_is_eq. Qed.

Lemma associator_is_eq {A B C D: Category} (F: C ~> D) (G: B ~> C) (H: A ~> B): is_eq (α F G H).
Proof. apply eq_iso_is_eq. Qed.

Lemma unitor_whisk_l {S T: Category} {F G: S ~> T} (η: F ~> G): λ G ∘ (id T <| η) = η ∘ λ F.
Proof.
  natural_eq x.
  rewrite (is_eq_refl (to (λ G) x)).
  rewrite (is_eq_refl (to (λ F) x)).
  rewrite comp_id_r.
  apply comp_id_l.
  apply (transform_is_eq (λ F)), unitor_l_is_eq.
  apply (transform_is_eq (λ G)), unitor_l_is_eq.
Qed.

Lemma unitor_whisk_r {S T: Category} {F G: S ~> T} (η: F ~> G): ρ G ∘ (η |> id S) = η ∘ ρ F.
Proof.
  natural_eq x.
  rewrite (is_eq_refl (to (ρ G) x)).
  rewrite (is_eq_refl (to (ρ F) x)).
  rewrite comp_id_r.
  apply comp_id_l.
  apply (transform_is_eq (ρ F)), unitor_r_is_eq.
  apply (transform_is_eq (ρ G)), unitor_r_is_eq.
Qed.

Lemma assoc_whisk_r {A B C D: Category} {H I: C ~> D} (η: H ~> I) (F: B ~> C) (G: A ~> B): α I F G ∘ (η |> (F ∘ G)) = ((η |> F) |> G) ∘ α H F G.
Proof.
  natural_eq x.
  rewrite (is_eq_refl (to (α I F G) x)).
  rewrite (is_eq_refl (to (α H F G) x)).
  rewrite comp_id_r.
  apply comp_id_l.
  apply (transform_is_eq (α H F G)), associator_is_eq.
  apply (transform_is_eq (α I F G)), associator_is_eq.
Qed.

Lemma assoc_whisk_l {A B C D: Category} {H I: A ~> B} (F: C ~> D) (G: B ~> C) (η: H ~> I): α F G I ∘ (F <| (G <| η)) = ((F ∘ G) <| η) ∘ α F G H.
Proof.
  natural_eq x.
  rewrite (is_eq_refl (to (α F G I) x)).
  rewrite (is_eq_refl (to (α F G H) x)).
  rewrite comp_id_r.
  apply comp_id_l.
  apply (transform_is_eq (α F G H)), associator_is_eq.
  apply (transform_is_eq (α F G I)), associator_is_eq.
Qed.

Lemma assoc_whisk {A B C D: Category} {H I: B ~> C} (F: C ~> D) (η: H ~> I) (G: A ~> B): α F I G ∘ (F <| (η |> G)) = ((F <| η) |> G) ∘ α F H G.
Proof.
  natural_eq x.
  rewrite (is_eq_refl (to (α F I G) x)).
  rewrite (is_eq_refl (to (α F H G) x)).
  rewrite comp_id_r.
  apply comp_id_l.
  apply (transform_is_eq (α F H G)), associator_is_eq.
  apply (transform_is_eq (α F I G)), associator_is_eq.
Qed.

Lemma assoc_unitor_r {A B C: Category} (F: B ~> C) (G: A ~> B): (ρ F |> G) ∘ α F (id B) G = F <| λ G.
Proof.
  natural_eq x.
  apply is_eq_unique.
  apply is_eq_comp.
  apply (transform_is_eq (α F (id B) G)), associator_is_eq.
  apply (transform_is_eq (ρ F)), unitor_r_is_eq.
  apply fmap_is_eq.
  apply (transform_is_eq (λ G)), unitor_l_is_eq.
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

Arguments diagonal: simpl never.

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

(*
Definition transport {C D: Category} {F G: C ~> D} {x y: C} (η: F <~> G) (f: F x ~> F y): G x ~> G y :=
  to η y ∘ f ∘ to η⁻¹ x.

Theorem transport_id_l {C D: Category} {F: C ~> D} {x y: C} (f: F x ~> F y): transport (id_iso F) f = f.
Proof.
  unfold transport.
  simpl.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Theorem transport_id_r {C D: Category} {F G: C ~> D} (η: F <~> G) (x: C): transport η (id (F x)) = id (G x).
Proof.
  unfold transport.
  rewrite <- fmap_id.
  rewrite naturality.
  rewrite <- comp_assoc.
  change (to η x ∘ to η⁻¹ x) with ((η ∘ η⁻¹) x).
  rewrite inv_r.
  simpl.
  rewrite comp_id_r.
  apply fmap_id.
Qed.

Theorem transport_comp {C D: Category} {F G H: C ~> D} {x y: C} (ϵ: G <~> H) (η: F <~> G) (f: F x ~> F y): transport (iso_comp ϵ η) f = transport ϵ (transport η f).
Proof.
  unfold transport; simpl.
  now rewrite !comp_assoc.
Qed.

Theorem transport_eq {C D: Category} {F G: C ~> D} {x y: C} (e: F = G) (f: x ~> y): transport (eq_iso e) (fmap F f) = fmap G f.
Proof.
  subst G.
  apply transport_id_l.
Qed.

Lemma fmap_transport {C D E: Category} {G H: C ~> D} {x y: C} (F: D ~> E) (η: G <~> H) (f: G x ~> G y): fmap F (transport η f) = transport (imov F η) (fmap F f).
Proof.
  unfold transport.
  now rewrite !fmap_comp.
Qed.

Lemma transport_inj {C D: Category} {F G: C ~> D} {x y: C} (η: F <~> G) (f g: F x ~> F y): transport η f = transport η g -> f = g.
Proof.
  intro H.
  unfold transport in H.
  apply iso_epic, iso_monic in H.
  exact H.
Qed.

Definition fmap' {C D: Category} {x y: C} (F: C <~> D) (f: to F x ~> Isomorphism.morphism F y): x ~> y :=
  transport (eq_iso (inv_l F)) (fmap (to F⁻¹) f).

Lemma fmap'_l {C D: Category} {x y: C} (F: C <~> D) (f: x ~> y): fmap' F (fmap (to F) f) = f.
Proof.
  change (transport (eq_iso (inv_l F)) (fmap (F⁻¹ ∘ F) f) = fmap (id C) f).
  apply transport_eq.
Qed.

Lemma fmap'_inj {C D: Category} {x y: C} (F: C <~> D) (f g: to F x ~> to F y): fmap' F f = fmap' F g -> f = g.
Proof.
  intros H.
  unfold fmap' in H.
  change (fmap (id D) f = fmap (id D) g).
  rewrite <- (inv_r F).
  simpl.
  f_equal.
  change (from F) with (to F⁻¹).
  revert H.
  generalize (eq_iso (inv_l F)).
  intros η.
  apply (transport_inj η).
Qed.

Lemma fmap'_r {C D: Category} {x y: C} (F: C <~> D) (f: to F x ~> to F y): fmap (to F) (fmap' F f) = f.
Proof.
  apply (fmap'_inj F).
  apply fmap'_l.
Qed.

Lemma mov_port {C: Category} {x y z: C} (i: y <~> z) (f: x ~> y): i⁻¹ ∘ (i ∘ f) = f.
Proof.
  rewrite comp_assoc.
  rewrite inv_l.
  apply comp_id_l.
Qed.

(*
Definition mov' {S T U: Category} {F G: S ~> T} (H: T <~> U) (η: H ∘ F ~> H ∘ G): F ~> G := transport (eq_iso (mov_port_eq H)) ∘ mov H⁻¹ η ∘ (eq_iso (mov_port H F))⁻¹.

Lemma mov'_l {S T U: Category} {F G: S ~> T} (H: T <~> U) (η: F ~> G): mov' H (mov H η) = η.
Proof.
  natural_eq x.
  change (eq_iso (mov_port H G))
  unfold mov'.
Qed.
*)
*)