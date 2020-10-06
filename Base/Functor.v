Require Export Isomorphism.

Structure Functor (C D: Category) := {
  fobj: C -> D;
  fmap {a b: C}: (a ~> b) -> fobj a ~> fobj b;
  fmap_id {a: C}: fmap (@id _ a) = @id _ (fobj a);
  fmap_comp {a b c: C} (f: b ~> c) (g: a ~> b): fmap (f ∘ g) = fmap f ∘ fmap g;
}.

Arguments fobj {C D}.
Arguments fmap {C D} _ {a b}.
Arguments fmap_id {C D _ a}.
Arguments fmap_comp {C D _ a b c}.

Coercion fobj: Functor >-> Funclass.

Theorem fun_eq {C D: Category} (F G: Functor C D): F = G <-> (forall x: C, F x = G x) /\ (forall (x y: C) (f: x ~> y) (ex: F x = G x) (ey: F y = G y), eq_iso ey ∘ fmap F f = fmap G f ∘ eq_iso ex).
Proof.
split.
+ intros H.
  subst G.
  split.
  intros x.
  reflexivity.
  intros x y f ex ey.
  rewrite !eq_iso_refl.
  simpl.
  rewrite comp_id_r.
  apply comp_id_l.
+ destruct F as [Fobj Fmap Fmap_id Fmap_comp], G as [Gobj Gmap Gmap_id Gmap_comp]; simpl.
  intros [Hobj Hmap].
  assert (Fobj = Gobj).
  now extensionality x.
  subst Gobj; clear Hobj.
  assert (Fmap = Gmap).
  extensionality x.
  extensionality y.
  extensionality f.
  specialize (Hmap x y f eq_refl eq_refl).
  simpl in Hmap.
  rewrite comp_id_l, comp_id_r in Hmap.
  exact Hmap.
  subst Gmap; clear Hmap.
  f_equal.
  all: apply proof_irrelevance.
Qed.

Ltac fun_eq x y f :=
match goal with
| [ |- ?F = ?G] =>
  apply (fun_eq F G); simpl;
  split; [
    intro;
    try reflexivity
  | let ex := fresh in
    let ey := fresh in
    intros x y f ex ey;
    try (
      rewrite (eq_iso_refl ex);
      clear ex;
      etransitivity; [ | symmetry; apply comp_id_r ]
    );
    try (
      rewrite (eq_iso_refl ey);
      clear ey;
      etransitivity; [ apply comp_id_l | ]
    );
    simpl
  ]
end.

Section Cat.

Definition fun_id (C: Category): Functor C C := {|
fobj x := x;
fmap a b f := f;
fmap_id a := eq_refl;
fmap_comp _ _ _ f g := eq_refl;
|}.

Definition fun_comp {C D E: Category} (F: Functor D E) (G: Functor C D): Functor C E := {|
fobj x := F (G x);
fmap a b f := fmap F (fmap G f);
fmap_id a := eq_trans (f_equal _ (fmap_id)) fmap_id;
fmap_comp _ _ _ f g := eq_trans (f_equal _ (fmap_comp f g)) (fmap_comp (fmap G f) (fmap G g));
|}.

Lemma fun_comp_assoc (A B C D: Category) (F: Functor C D) (G: Functor B C) (H: Functor A B): fun_comp F (fun_comp G H) = fun_comp (fun_comp F G) H.
Proof. now fun_eq x y f. Qed.

Lemma fun_comp_id_l (A B: Category) (F: Functor A B): fun_comp (fun_id B) F = F.
Proof. now fun_eq x y f. Qed.

Lemma fun_comp_id_r (A B: Category) (F: Functor A B): fun_comp F (fun_id A) = F.
Proof. now fun_eq x y f. Qed.

Definition Cat_mixin: Category.mixin_of Category :=
Category.Mixin Category Functor fun_id (@fun_comp) fun_comp_assoc fun_comp_id_l fun_comp_id_r.

Global Canonical Cat: Category :=
Category.Pack Category Cat_mixin.

End Cat.

Section fmap_iso.
Context {C D: Category} {x y: C} (F: C ~> D) (i: x <~> y).

Definition imap_mixin: Isomorphism.mixin_of (fmap F i) :=
Isomorphism.Mixin _ _ _ (fmap F i) (fmap F i⁻¹)
(eq_trans (eq_sym (fmap_comp _ _)) (eq_trans (f_equal _ (inv_l _)) fmap_id))
(eq_trans (eq_sym (fmap_comp _ _)) (eq_trans (f_equal _ (inv_r _)) fmap_id)).

Global Canonical imap: F x <~> F y :=
Isomorphism.Pack (fmap F i) imap_mixin.

End fmap_iso.

Lemma is_iso_fmap {C D: Category} {x y: C} (F: C ~> D) (f: x ~> y): is_iso f -> is_iso (fmap F f).
Proof.
  intros [g [Hl Hr]].
  exists (fmap F g); split.
  all: rewrite <- fmap_comp, <- fmap_id.
  all: now f_equal.
Qed.

Lemma fmap_is_eq {C D: Category} {x y: C} (F: C ~> D) (f: x ~> y): is_eq f -> is_eq (fmap F f).
Proof.
intros [e H].
subst f y.
simpl.
rewrite fmap_id.
apply is_eq_id.
Qed.

Theorem fmap_inv {C D: Category} {x y: C} (F: C ~> D) (i: x <~> y): fmap F (i⁻¹) = (imap F i)⁻¹.
Proof. reflexivity. Qed.

Theorem imap_inv {C D: Category} {x y: C} (F: C ~> D) (i: x <~> y): imap F (i⁻¹) = (imap F i)⁻¹.
Proof. now apply iso_eq. Qed.

Definition cof {S T: Category} (F: S ~> T): co S ~> co T := {|
  fobj (x: co S) := F x: co T;
  fmap x y f := fmap F f;
  fmap_id := @fmap_id _ _ F;
  fmap_comp _ _ _ f g := @fmap_comp _ _ F _ _ _ g f;
|}.

Definition cof' {S T: Category} (F: co S ~> co T): S ~> T := {|
  fobj (x: S) := F x: T;
  fmap x y f := fmap F f;
  fmap_id := @fmap_id _ _ F;
  fmap_comp _ _ _ f g := @fmap_comp _ _ F _ _ _ g f;
|}.

Lemma cof_inv_l {S T: Category} (F: S ~> T): cof' (cof F) = F.
Proof. now fun_eq x y f. Qed.

Lemma cof_inv_r {S T: Category} (F: co S ~> co T): cof (cof' F) = F.
Proof.
  fun_eq x y f.
  rewrite !eq_iso_refl.
  unfold inv; simpl.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Instance co_iso: Proper (isomorphic Cat ==> isomorphic Cat) co.
Proof.
  intros C D [[F [G]]].
  constructor.
  exists (cof F), (cof G).
  1: clear inv_r.
  2: clear inv_l.
  1: apply fun_eq in inv_l.
  2: apply fun_eq in inv_r.
  1: destruct inv_l as [Ho Hf].
  2: destruct inv_r as [Ho Hf].
  all: fun_eq y x f.
  1, 3: apply Ho.
  all: clear Ho.
  all: change (x ~> y) in f.
  all: unfold comp; simpl.
  all: change (Category.comp (Category.obj ?C) _ ?f ?g) with (@comp C _ _ _ f g).
  all: specialize (Hf x y f H0 H).
  all: simpl in Hf.
  all: rewrite !co_eq_iso.
  all: apply (iso_epic (eq_iso H0)).
  all: rewrite <- !comp_assoc.
  all: rewrite inv_l, comp_id_r.
  all: apply (iso_monic (eq_iso H)).
  all: rewrite comp_assoc.
  all: rewrite inv_r, comp_id_l.
  all: exact Hf.
Qed.

Definition full {S T: Category} (F: S ~> T) :=
  forall (x y: S) (f: F x ~> F y), exists f': x ~> y, fmap F f' = f.

Definition faithful {S T: Category} (F: S ~> T) :=
  forall (x y: S) (f g: x ~> y), fmap F f = fmap F g -> f = g.

Definition fully_faithful {S T: Category} (F: S ~> T) :=
  full F /\ faithful F.

Lemma fully_faithful_maps_iso {S T: Category} {x y: S} (F: S ~> T) (f: x ~> y): fully_faithful F -> is_iso f <-> is_iso (fmap F f).
Proof.
  intros [H0 H1].
  split.
  apply is_iso_fmap.
  intros [g' H].
  specialize (H0 y x g').
  destruct H0 as [g H0].
  subst g'.
  rewrite <- !fmap_comp in H.
  rewrite <- !fmap_id in H.
  exists g.
  split; [apply proj1 in H | apply proj2 in H].
  all: apply H1, H.
Qed.

Lemma fully_faithful_iso {S T: Category} (F: S ~> T) (x y: S): fully_faithful F -> x ≃ y <-> F x ≃ F y.
Proof.
  intros [H0 H1].
  split.
  all: intros [i].
  constructor.
  apply imap, i.
  destruct (H0 x y i) as [f Hf].
  destruct (H0 y x i⁻¹) as [g Hg].
  constructor.
  exists f, g.
  all: apply H1.
  all: rewrite fmap_id, fmap_comp.
  all: rewrite Hf, Hg.
  apply inv_l.
  apply inv_r.
Qed.

Lemma full_id (C: Category): full (id C).
Proof.
  intros x y f.
  now exists f.
Qed.

Lemma faithful_id (C: Category): faithful (id C).
Proof. easy. Qed.

Lemma fully_faithful_id (C: Category): fully_faithful (id C).
Proof.
  split.
  apply full_id.
  apply faithful_id.
Qed.

Lemma full_comp {A B C: Category} (F: B ~> C) (G: A ~> B): full F -> full G -> full (F ∘ G).
Proof.
  intros HF HG x y f.
  simpl in f |- *.
  specialize (HF (G x) (G y) f).
  destruct HF as [f' H].
  subst f.
  specialize (HG x y f').
  destruct HG as [f H].
  subst f'.
  now exists f.
Qed.

Lemma faithful_comp {A B C: Category} (F: B ~> C) (G: A ~> B): faithful F -> faithful G -> faithful (F ∘ G).
Proof.
  intros HF HG x y f g H.
  apply HG, HF, H.
Qed.

Lemma fully_faithful_comp {A B C: Category} (F: B ~> C) (G: A ~> B): fully_faithful F -> fully_faithful G -> fully_faithful (F ∘ G).
Proof.
  intros [HF1 HF2] [HG1 HG2].
  split.
  now apply full_comp.
  now apply faithful_comp.
Qed.

Lemma full_cof {S T: Category} (F: S ~> T): full F -> full (cof F).
Proof.
  intros H x y f.
  apply H.
Qed.

Lemma faithful_cof {S T: Category} (F: S ~> T): faithful F -> faithful (cof F).
Proof.
  intros H x y f g.
  apply H.
Qed.

Lemma fully_faithful_cof {S T: Category} (F: S ~> T): fully_faithful F -> fully_faithful (cof F).
Proof.
  intros [H0 H1].
  split.
  now apply full_cof.
  now apply faithful_cof.
Qed.

Lemma full_cof' {S T: Category} (F: co S ~> co T): full F -> full (cof' F).
Proof.
  intros H x y f.
  apply H.
Qed.

Lemma faithful_cof' {S T: Category} (F: co S ~> co T): faithful F -> faithful (cof' F).
Proof.
  intros H x y f g.
  apply H.
Qed.

Lemma fully_faithful_cof' {S T: Category} (F: co S ~> co T): fully_faithful F -> fully_faithful (cof' F).
Proof.
  intros [H0 H1].
  split.
  now apply full_cof'.
  now apply faithful_cof'.
Qed.

Definition esurj {S T: Category} (F: S ~> T) :=
  forall y: T, exists x: S, F x ≃ y.

Lemma esurj_id (C: Category): esurj (id C).
Proof.
  intros x.
  now exists x.
Qed.

Lemma esurj_comp {A B C: Category} (F: B ~> C) (G: A ~> B): esurj F -> esurj G -> esurj (F ∘ G).
Proof.
  intros HF HG z.
  specialize (HF z).
  destruct HF as [y HF].
  specialize (HG y).
  destruct HG as [x HG].
  exists x.
  simpl.
  rewrite <- HF; clear HF.
  destruct HG as [i].
  constructor.
  exact (imap F i).
Qed.

Lemma esurj_cof {S T: Category} (F: S ~> T): esurj F <-> esurj (cof F).
Proof.
  split.
  all: intros H y.
  all: specialize (H y).
  all: destruct H as [x H].
  all: exists x.
  all: simpl in H |- *.
  1: rewrite iso_co.
  2: rewrite <- iso_co.
  all: exact H.
Qed.

Lemma esurj_cof' {S T: Category} (F: co S ~> co T): esurj F <-> esurj (cof' F).
Proof.
  split.
  all: intros H y.
  all: specialize (H y).
  all: destruct H as [x H].
  all: exists x.
  all: simpl in H |- *.
  1: rewrite <- iso_co.
  2: rewrite iso_co.
  all: exact H.
Qed.
