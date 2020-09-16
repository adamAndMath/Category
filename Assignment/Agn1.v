Require Export Monad.
Require Export Sets.Rel.
Require Export Sets.Sets.

Section ex1.
Program Definition T: SET ~> SET := {|
  fobj := pow;
  fmap X Y f := setf_of (fun A => { map f x | x ⋴ A }) _;
|}.
Next Obligation.
  apply in_pow in H.
  apply in_pow.
  intros z Hz.
  apply in_map in Hz.
  destruct Hz as [y [Hy Hz]].
  subst z.
  apply mapto, H, Hy.
Qed.
Next Obligation.
  rename a into A.
  apply setf_eq.
  intros x Hx.
  rewrite !(map_ap _ _ Hx).
  simpl.
  apply antisymmetry.
  all: intros z Hz.
  + apply in_map in Hz.
    destruct Hz as [y [Hy Hz]].
    subst z.
    apply in_pow in Hx.
    specialize (Hx y Hy).
    now rewrite (map_ap _ _ Hx).
  + apply in_map.
    exists z.
    split.
    exact Hz.
    apply in_pow in Hx.
    specialize (Hx z Hz).
    rewrite (map_ap _ _ Hx).
    reflexivity.
Qed.
Next Obligation.
  apply setf_eq.
  intros x Hx.
  rewrite !(map_ap _ _ Hx).
  simpl.
  rewrite map_comp.
  apply set_eq_ext.
  intros z.
  rewrite !in_map.
  f_equiv; intros y.
  enough (y ∈ x -> map (fun x0 : {x0 : set | x0 ∈ a} => f (g x0)) y = map f (map g y)).
  split.
  1, 2: intros [Hy Hz].
  1, 2: split; [exact Hy | ].
  1, 2: subst z.
  2: symmetry.
  1, 2: apply H, Hy.
  intros Hy.
  apply in_pow in Hx.
  specialize (Hx y Hy).
  specialize (mapto g y Hx) as Hg.
  rewrite !(map_ap _ _ Hx) in Hg.
  rewrite !(map_ap _ _ Hx).
  rewrite (map_ap _ _ Hg).
  do 2 f_equal.
  now apply eq_sig.
Qed.
End ex1.

Section ex2.

Definition T_lift: id SET ~> T.
Proof.
  unshelve econstructor; simpl.
  intros X.
  refine (setf_of single _).
  intros x Hx.
  apply in_pow.
  intros z Hz.
  apply in_single in Hz.
  subst z.
  exact Hx.
  intros X Y f.
  simpl.
  apply setf_eq.
  intros x Hx.
  rewrite !(map_ap _ _ Hx).
  simpl.
  rewrite <- map_ap.
  symmetry.
  apply map_single.
Defined.

Definition T_flatten: T ∘ T ~> T.
Proof.
  unshelve econstructor; simpl.
  intros X.
  refine (setf_of union _).
  intros x Hx.
  apply in_pow.
  intros z Hz.
  apply in_union in Hz.
  destruct Hz as [y [Hy Hz]].
  apply in_pow in Hx.
  apply Hx in Hy.
  apply in_pow in Hy.
  apply Hy, Hz.
  intros X Y f.
  simpl.
  apply setf_eq.
  intros x Hx.
  rewrite !(map_ap _ _ Hx).
  simpl.
  apply in_pow in Hx.
  apply antisymmetry.
  all: intros z Hz.
  + apply in_flat_map in Hz.
    destruct Hz as [y [Hy Hz]].
    specialize (Hx _ Hy).
    rewrite (map_ap _ _ Hx) in Hz.
    simpl in Hz.
    apply in_map in Hz.
    destruct Hz as [p [Hp Hz]].
    subst z.
    apply in_map'.
    apply in_union.
    now exists y.
  + apply in_map in Hz.
    destruct Hz as [y [Hy Hz]].
    subst z.
    apply in_union in Hy.
    destruct Hy as [z [Hz Hy]].
    apply in_flat_map.
    exists z.
    split.
    exact Hz.
    apply Hx in Hz.
    rewrite (map_ap _ _ Hz).
    simpl.
    apply in_map', Hy.
Defined.

Lemma T_flatten_comm (X: set): T_flatten X ∘ fmap T (T_flatten X) = T_flatten X ∘ T_flatten (T X).
Proof.
  apply setf_eq.
  intros x Hx.
  rewrite !(map_ap _ _ Hx).
  simpl.
  apply in_pow in Hx.
  apply antisymmetry.
  all: intros z Hz.
  + apply in_flat_map in Hz.
    destruct Hz as [y [Hy Hz]].
    specialize (Hx _ Hy).
    rewrite (map_ap _ _ Hx) in Hz.
    simpl in Hz.
    apply in_union in Hz.
    destruct Hz as [v [Hv Hz]].
    apply in_union.
    exists v; split.
    apply in_union.
    exists y; split.
    all: assumption.
  + apply in_union in Hz.
    destruct Hz as [y [Hy Hz]].
    apply in_union in Hy.
    destruct Hy as [v [Hv Hy]].
    apply in_flat_map.
    exists v.
    split.
    exact Hv.
    rewrite (map_ap _ _ (Hx v Hv)).
    simpl.
    apply in_union.
    now exists y.
Qed.

Lemma T_flatten_lift_l (X: set): T_flatten X ∘ T_lift (T X) = id (T X).
Proof.
  apply setf_eq; simpl.
  intros x Hx.
  rewrite !(map_ap _ _ Hx).
  simpl.
  apply union_single.
Qed.

Lemma T_flatten_lift_r (X: set): T_flatten X ∘ fmap T (T_lift X) = id (T X).
Proof.
  apply setf_eq; simpl.
  intros x Hx.
  rewrite !(map_ap _ _ Hx).
  simpl.
  apply in_pow in Hx.
  apply antisymmetry.
  all: intros z Hz.
  + apply in_flat_map in Hz.
    destruct Hz as [y [Hy Hz]].
    rewrite (map_ap _ _ (Hx y Hy)) in Hz.
    simpl in Hz.
    apply in_single in Hz.
    now subst z.
  + apply in_flat_map.
    exists z.
    split.
    exact Hz.
    rewrite (map_ap _ _ (Hx z Hz)).
    simpl.
    now apply in_single.
Qed.

Definition T_monad_mixin: Monad.mixin_of T :=
  Monad.Mixin SET T T_lift T_flatten T_flatten_comm T_flatten_lift_l T_flatten_lift_r.

Global Canonical T_monad: Monad SET :=
  Monad.Pack SET T T_monad_mixin.

Definition K: Category := MCat T_monad.

Lemma K_comp_correct {X Y Z: K} (g: Y ~> Z) (f: X ~> Y) x: x ∈ X -> map (g ∘ f) x = ∪ {map g y | y ⋴ map f x}.
Proof.
  intros Hx.
  rewrite (map_ap _ _ Hx).
  simpl.
  rewrite <- map_ap.
  reflexivity.
Qed.

Program Definition K_to_Rel: K ~> REL := {|
  fobj X := X;
  fmap X Y f x y := x ∈ X /\ y ∈ map f x;
|}.
Next Obligation.
  split.
  exact H.
  apply (mapto f) in H.
  apply in_pow in H.
  apply H, H0.
Qed.
Next Obligation.
  rel_eq x y.
  split.
  all: intros [Hx Hy].
  all: split; [exact Hx | ].
  rewrite (map_ap _ _ Hx) in Hy.
  simpl in Hy.
  symmetry.
  apply in_single, Hy.
  subst y.
  rewrite (map_ap _ _ Hx).
  simpl.
  now apply in_single.
Qed.
Next Obligation.
  rel_eq x z.
  split.
  + intros [Hx Hz].
    rewrite (map_ap _ _ Hx) in Hz.
    simpl in Hz.
    apply in_flat_map in Hz.
    destruct Hz as [y [Hy Hz]].
    rewrite <- map_ap in Hy.
    exists y.
    repeat split.
    apply (mapto g) in Hx.
    apply in_pow in Hx.
    apply Hx, Hy.
    all: assumption.
  + intros [y [[Hyb Hz] [Hx Hy]]].
    split.
    exact Hx.
    rewrite (map_ap _ _ Hx).
    simpl.
    apply in_flat_map.
    exists y; split.
    rewrite <- map_ap.
    all: assumption.
Qed.

Program Definition Rel_to_K: REL ~> K := {|
  fobj X := X;
  fmap X Y f x := { y ⋴ Y | f x y};
|}.
Next Obligation.
  apply in_pow.
  intros y Hy.
  now apply in_sep in Hy.
Qed.
Next Obligation.
  extensionality x.
  apply eq_sig.
  simpl.
  apply set_eq_ext.
  intros y.
  rewrite in_sep, in_single.
  split.
  now intros [_ [_ H]].
  intros H.
  subst y.
  repeat split.
  1, 2: apply proj2_sig.
Qed.
Next Obligation.
  apply setf_eq.
  intros x Hx.
  rewrite !(map_ap _ _ Hx).
  simpl.
  apply set_eq_ext.
  intros z.
  rewrite in_sep, in_flat_map.
  split.
  + intros [Hz [y [yz xy]]].
    assert (Hy: y ∈ b).
    apply (proj2_sig g x y xy).
    exists y.
    split.
    now apply in_sep.
    rewrite (map_ap _ _ Hy).
    simpl.
    now apply in_sep.
  + intros [y [Hy Hz]].
    apply in_sep in Hy.
    destruct Hy as [Hy xy].
    rewrite (map_ap _ _ Hy) in Hz.
    simpl in Hz.
    apply in_sep in Hz.
    destruct Hz as [Hz yz].
    split; [exact Hz | ].
    now exists y.
Qed.

Lemma KRel_inv_l: Rel_to_K ∘ K_to_Rel = id K.
Proof.
  fun_eq X Y f.
  rewrite !eq_iso_refl.
  unfold inv; simpl.
  rewrite comp_id_r.
  rewrite comp_id_l.
  clear H H0.
  apply setf_eq.
  intros x Hx.
  rewrite (map_ap _ _ Hx).
  simpl.
  apply antisymmetry.
  all: intros z Hz.
  + apply in_sep in Hz.
    now destruct Hz as [_ [_ H]].
  + apply in_sep.
    repeat split.
    apply (mapto f) in Hx.
    apply in_pow in Hx.
    apply Hx, Hz.
    all: assumption.
Qed.

Lemma KRel_inv_r: K_to_Rel ∘ Rel_to_K = id REL.
Proof.
  fun_eq X Y f.
  rewrite !eq_iso_refl.
  unfold inv; simpl.
  rewrite comp_id_r.
  rewrite comp_id_l.
  clear H H0.
  rel_eq x y.
  split.
  + intros [Hx Hy].
    rewrite (map_ap _ _ Hx) in Hy.
    simpl in Hy.
    now apply in_sep in Hy.
  + intros xy.
    specialize (proj2_sig f x y xy) as [Hx Hy].
    split.
    exact Hx.
    rewrite (map_ap _ _ Hx).
    simpl.
    now apply in_sep.
Qed.

Definition iso_KRel_mixin: Isomorphism.mixin_of K_to_Rel :=
  Isomorphism.Mixin Cat K REL K_to_Rel Rel_to_K KRel_inv_l KRel_inv_r.

Definition iso_KRel: iso K REL :=
  Isomorphism.Pack K_to_Rel iso_KRel_mixin.
End ex2.

Section ex3.

Lemma pi1_not_monic: ~forall A B: set, @monic SET (A × B) A π₁.
Proof.
  unfold monic.
  enough (exists (A B C: set) (g1 g2: C ~> A × B), @π₁ _ A B ∘ g1 = π₁ ∘ g2 /\ ~(g1 = g2)).
  destruct H as [A [B [C [g1 [g2 [H n]]]]]].
  contradict n.
  eapply n, H.
  exists (single Ø).
  exists {Ø, single Ø}.
  exists (single Ø).
  1: unshelve eexists.
  2: unshelve eexists.
  1, 2: apply fork.
  1, 3: apply id.
  1: refine (setf_of (fun _ => Ø) _).
  2: refine (setf_of (fun _ => single Ø) _).
  1, 2: intros x Hx.
  1, 2: apply in_single in Hx.
  1, 2: subst x.
  1, 2: apply in_upair.
  now left.
  now right.
  simpl.
  generalize (
    (fun (x0 : set) (_ : x0 ∈ single Ø) =>
      match in_upair Ø Ø (single Ø) with
      | conj _ H => H
      end (or_introl eq_refl))
  ) (
    (fun (x0 : set) (_ : x0 ∈ single Ø) =>
      match in_upair (single Ø) Ø (single Ø) with
      | conj _ H => H
      end (or_intror eq_refl))
  ).
  intros HØ Hs.
  split.
  apply setf_eq.
  intros x Hx.
  rewrite !(map_ap _ _ Hx).
  simpl.
  rewrite !(map_ap _ _ Hx).
  simpl.
  apply in_single in Hx.
  subst x.
  rewrite !intersect_pair.
  reflexivity.
  intros H.
  rewrite setf_eq in H.
  assert (H0: Ø ∈ single Ø).
  now apply in_single.
  specialize (H Ø H0).
  rewrite !(map_ap _ _ H0) in H.
  simpl in H.
  rewrite !(map_ap _ _ H0) in H.
  simpl in H.
  apply pair_inj, proj2 in H.
  symmetry in H.
  contradict H.
  apply single_not_empty.
Qed.

Lemma pi1_not_epic: ~forall A B: set, @epic SET (A × B) A π₁.
Proof.
  unfold epic.
  enough (exists (A B C: set) (g1 g2: A ~> C), g1 ∘ @π₁ _ A B = g2 ∘ π₁ /\ ~(g1 = g2)).
  destruct H as [A [B [C [g1 [g2 [H n]]]]]].
  contradict n.
  eapply n, H.
  exists (single Ø), Ø.
  exists {Ø, single Ø}.
  1: unshelve eexists (fun _ => exist _ Ø _).
  2: unshelve eexists (fun _ => exist _ (single Ø) _).
  all: simpl.
  1, 2: apply in_upair.
  now left.
  now right.
  simpl.
  split.
  apply setf_eq.
  intros x Hx.
  rewrite !(map_ap _ _ Hx).
  simpl.
  apply in_cartisian in Hx.
  destruct Hx as [_ [z [_ [Hz _]]]].
  contradict Hz.
  apply in_empty.
  intros H.
  rewrite setf_eq in H.
  assert (HØ: Ø ∈ single Ø).
  now apply in_single.
  specialize (H Ø HØ).
  rewrite !(map_ap _ _ HØ) in H.
  simpl in H.
  symmetry in H.
  contradict H.
  apply single_not_empty.
Qed.

Lemma fork_pi_id {C: ProdCategory} {a b: C}: ⟨π₁, π₂⟩ = @id C (a × b).
Proof.
  rewrite <- (fork_eta (id (a × b))).
  f_equal.
  all: symmetry.
  all: apply comp_id_r.
Qed.

Lemma comp_fork {C: ProdCategory} {a b c d: C} (f : b ~> c) (g: b ~> d) (h: a ~> b):
  ⟨f, g⟩ ∘ h = ⟨f ∘ h, g ∘ h⟩.
Proof.
  rewrite <- (fork_eta _).
  f_equal.
  all: rewrite comp_assoc.
  now rewrite pi1_fork.
  now rewrite pi2_fork.
Qed.

Definition lift {C: ProdCategory} {a b c d: C} (f: a ~> c) (g: b ~> d): a × b ~> c × d :=
  ⟨f ∘ π₁, g ∘ π₂⟩.

Lemma lift_correct {C: ProdCategory} {a b c d e: C} (f: b ~> d) (g: c ~> e) (h1: a ~> b) (h2: a ~> c):
  lift f g ∘ ⟨h1, h2⟩ = ⟨f ∘ h1, g ∘ h2⟩.
Proof.
  unfold lift.
  rewrite comp_fork.
  f_equiv.
  all: rewrite <- comp_assoc.
  all: f_equiv.
  apply pi1_fork.
  apply pi2_fork.
Qed.

Lemma lift_unique {C: ProdCategory} {a b c d: C} (f: a ~> c) (g: b ~> d) (u: a × b ~> c × d):
  (forall x (h1: x ~> a) (h2: x ~> b), u ∘ ⟨h1, h2⟩ = ⟨f ∘ h1, g ∘ h2⟩) ->
  lift f g = u.
Proof.
  intros H.
  unfold lift.
  rewrite <- H.
  rewrite <- (comp_id_r u) at 2.
  f_equiv.
  apply fork_pi_id.
Qed.

Lemma lift_comp {C: ProdCategory} {a1 a2 b1 b2 c1 c2: C} (f1: a1 ~> b1) (f2: a2 ~> b2) (g1: b1 ~> c1) (g2: b2 ~> c2):
  lift g1 g2 ∘ lift f1 f2 = lift (g1 ∘ f1) (g2 ∘ f2).
Proof.
  unfold lift.
  rewrite comp_fork.
  f_equiv.
  all: rewrite <- !comp_assoc.
  all: f_equiv.
  apply pi1_fork.
  apply pi2_fork.
Qed.

End ex3.
