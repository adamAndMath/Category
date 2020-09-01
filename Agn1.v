Require Export Sets.Rel.
Require Export Sets.Sets.

Section ex1.
Program Definition T: Sets ~~> Sets := {|
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
  apply eq_sig_hprop.
  intro.
  apply proof_irrelevance.
  reflexivity.
Qed.

Section ex2.
Program Definition K: Category := {|
  obj := Sets;
  hom X Y := X ~> (T Y);
  id X := setf_of single _;
  comp X Y Z g f := setf_of (fun x => ∪ {map g y | y ⋴ map f x}) _;
|}.
Next Obligation.
  apply in_pow.
  intros z Hz.
  apply in_single in Hz.
  now subst z.
Qed.
Next Obligation.
  apply in_pow.
  intros z Hz.
  apply in_flat_map in Hz.
  destruct Hz as [y [Hy Hz]].
  apply (mapto f) in H.
  apply in_pow in H.
  apply H in Hy.
  apply (mapto g) in Hy.
  apply in_pow in Hy.
  apply Hy, Hz.
Qed.
Next Obligation.
  apply setf_eq.
  intros x Hx.
  rewrite !(map_ap _ _ Hx).
  simpl.
  apply antisymmetry.
  + intros z Hz.
    apply in_flat_map in Hz.
    destruct Hz as [y [Hy Hz]].
    rewrite (map_ap _ _ Hx) in Hy.
    simpl in Hy.
    apply in_flat_map in Hy.
    destruct Hy as [v [Hv Hy]].
    apply in_flat_map.
    exists v.
    split.
    exact Hv.
    assert (v ∈ b).
    apply (mapto h) in Hx.
    apply in_pow in Hx.
    apply Hx, Hv.
    rewrite (map_ap _ _ H).
    simpl.
    apply in_flat_map.
    now exists y.
  + intros z Hz.
    apply in_flat_map in Hz.
    destruct Hz as [y [Hy Hz]].
    assert (y ∈ b).
    apply (mapto h) in Hx.
    apply in_pow in Hx.
    apply Hx, Hy.
    rewrite (map_ap _ _ H) in Hz.
    apply in_flat_map in Hz.
    destruct Hz as [v [Hv Hz]].
    apply in_flat_map.
    exists v.
    split.
    rewrite (map_ap _ _ Hx).
    simpl.
    apply in_flat_map.
    now exists y.
    exact Hz.
Qed.
Next Obligation.
  apply setf_eq.
  intros x Hx.
  rewrite (map_ap _ _ Hx).
  simpl.
  apply antisymmetry.
  + intros z Hz.
    apply in_flat_map in Hz.
    destruct Hz as [y [Hy Hz]].
    assert (y ∈ b).
    apply (mapto f) in Hx.
    apply in_pow in Hx.
    apply Hx, Hy.
    rewrite (map_ap _ _ H) in Hz.
    simpl in Hz.
    apply in_single in Hz.
    now subst z.
  + intros z Hz.
    apply in_flat_map.
    exists z.
    split.
    exact Hz.
    assert (z ∈ b).
    apply (mapto f) in Hx.
    apply in_pow in Hx.
    apply Hx, Hz.
    rewrite (map_ap _ _ H).
    now apply in_single.
Qed.
Next Obligation.
  apply setf_eq.
  intros x Hx.
  rewrite (map_ap _ _ Hx).
  simpl.
  rewrite (map_ap _ _ Hx).
  simpl.
  rewrite map_single.
  apply union_single.
Qed.

Program Definition K_to_Rel: K ~~> Rel := {|
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
  extensionality x.
  extensionality y.
  apply eq_sig_hprop.
  intro.
  apply proof_irrelevance.
  simpl.
  apply propositional_extensionality.
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
  extensionality x.
  extensionality z.
  apply eq_sig_hprop.
  intro.
  apply proof_irrelevance.
  simpl.
  apply propositional_extensionality.
  split.
  + intros [Hx Hz].
    rewrite (map_ap _ _ Hx) in Hz.
    simpl in Hz.
    apply in_flat_map in Hz.
    destruct Hz as [y [Hy Hz]].
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
    now exists y.
Qed.

Program Definition Rel_to_K: Rel ~~> K := {|
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
  apply eq_sig_hprop.
  intro.
  apply proof_irrelevance.
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
  extensionality x.
  apply eq_sig_hprop.
  intro.
  apply proof_irrelevance.
  simpl.
  destruct x as [x Hx].
  simpl.
  rewrite (map_ap _ _ Hx).
  simpl.
  apply set_eq_ext.
  intros z.
  rewrite in_sep, in_flat_map.
  split.
  + intros [Hz [y [yz xy]]].
    assert (Hy: y ∈ b).
    apply (proj2_sig (g x y)), xy.
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

Program Definition iso_KRel: @iso Cat K Rel := {|
  to := K_to_Rel;
  from := Rel_to_K;
|}.
Next Obligation.
  apply fun_eq; simpl.
  split; [easy | ].
  intros X Y f ex ey.
  rewrite !eq_iso_refl.
  clear ex ey.
  apply setf_eq.
  intros x Hx.
  simpl.
  rewrite (map_ap _ _ Hx).
  simpl.
  apply antisymmetry.
  + intros z Hz.
    apply in_flat_map in Hz.
    destruct Hz as [y [Hy Hz]].
    rewrite (map_ap _ _ Hx) in Hy.
    simpl in Hy.
    apply in_single in Hy.
    subst y.
    rewrite (map_ap _ _ Hx) in Hz.
    simpl in Hz.
    apply in_flat_map in Hz.
    destruct Hz as [y [Hy Hz]].
    rewrite (map_ap _ _ Hx) in Hy.
    simpl in Hy.
    apply in_sep in Hy.
    destruct Hy as [Hy [_ H]].
    rewrite (map_ap _ _ Hy) in Hz.
    simpl in Hz.
    apply in_single in Hz.
    now subst y.
  + intros z Hz.
    apply in_flat_map.
    exists x.
    split.
    all: rewrite (map_ap _ _ Hx).
    all: simpl.
    now apply in_single.
    apply in_flat_map.
    assert (z ∈ Y).
    apply (mapto f) in Hx.
    apply in_pow in Hx.
    apply Hx, Hz.
    exists z.
    split.
    rewrite (map_ap _ _ Hx).
    simpl.
    now apply in_sep.
    rewrite (map_ap _ _ H).
    simpl.
    now apply in_single.
Qed.
Next Obligation.
  apply fun_eq; simpl.
  split; [easy | ].
  intros X Y f ex ey.
  rewrite !eq_iso_refl.
  clear ex ey.
  extensionality x.
  extensionality y.
  apply eq_sig_hprop.
  intro.
  apply proof_irrelevance.
  simpl.
  apply propositional_extensionality.
  split.
  + intros [x' [[y' [[Hy Hy'] [_ H]]] [Hx Hx']]].
    subst x' y'.
    rewrite (map_ap _ _ Hx) in H.
    simpl in H.
    now apply in_sep in H.
  + intros xy.
    specialize (proj2_sig (f x y) xy) as [Hx Hy].
    exists x.
    repeat split.
    exists y.
    repeat split.
    1, 2, 4: assumption.
    rewrite (map_ap _ _ Hx).
    simpl.
    now apply in_sep.
Qed.
End ex2.

Section ex3.

Lemma pi1_not_monic: ~forall A B: Sets, @monic Sets (A × B) A π₁.
Proof.
  unfold monic.
  enough (exists (A B C: Sets) (g1 g2: C ~> A × B), @π₁ _ A B ∘ g1 = π₁ ∘ g2 /\ ~(g1 = g2)).
  destruct H as [A [B [C [g1 [g2 [H n]]]]]].
  contradict n.
  eapply n, H.
  exists (single Ø).
  exists {Ø, single Ø}.
  exists (single Ø).
  1: unshelve eexists.
  2: unshelve eexists.
  1, 2: apply join.
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
  unfold join; simpl; unfold set_join.
  generalize (
    (Sets.set_join_obligation_1 (single Ø) (single Ø) 
     {Ø, single Ø} (fun x : {x : set | x ∈ single Ø} => x)
     (setf_of (fun _ : set => Ø) HØ))
  ) (
    (Sets.set_join_obligation_1 (single Ø) (single Ø) 
     {Ø, single Ø} (fun x : {x : set | x ∈ single Ø} => x)
     (setf_of (fun _ : set => single Ø) Hs))
  ).
  intros H1 H2 H.
  assert (forall x,
    setf_of
      (fun x : set =>
       pair (map (fun x0 : {x0 : set | x0 ∈ single Ø} => x0) x)
         (map (setf_of (fun _ : set => Ø) HØ) x)) H1 x =
    setf_of
      (fun x : set =>
       pair (map (fun x0 : {x0 : set | x0 ∈ single Ø} => x0) x)
         (map (setf_of (fun _ : set => single Ø) Hs) x)) H2 x

  ).
  now rewrite H.
  clear H; rename H0 into H.
  specialize (H (exist _ Ø (proj2 (in_single _ _) eq_refl))).
  unfold setf_of in H; simpl in H.
  apply eq_sig_fst in H.
  clear - H.
  rewrite !(map_ap _ _ (proj2 (in_single _ _) eq_refl)) in H.
  simpl in H.
  apply pair_inj, proj2 in H.
  symmetry in H.
  contradict H.
  apply single_not_empty.
Qed.

Lemma pi1_not_epic: ~forall A B: Sets, @epic Sets (A × B) A π₁.
Proof.
  unfold epic.
  enough (exists (A B C: Sets) (g1 g2: A ~> C), g1 ∘ @π₁ _ A B = g2 ∘ π₁ /\ ~(g1 = g2)).
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
  extensionality x.
  destruct x as [x Hx].
  apply in_cartisian in Hx.
  destruct Hx as [_ [y [_ [Hy _]]]].
  now apply in_empty in Hy.
  intros H.
  cut (forall x,
    (fun _ : {x : set | x ∈ single Ø} =>
     exist (fun y : set => y ∈ {Ø, single Ø}) Ø
       (match in_upair Ø Ø (single Ø) with
        | conj _ x => x
        end (or_introl eq_refl))) x =
    (fun _ : {x : set | x ∈ single Ø} =>
     exist (fun y : set => y ∈ {Ø, single Ø}) (single Ø)
       (match in_upair (single Ø) Ø (single Ø) with
        | conj _ x => x
        end (or_intror eq_refl))) x
  ).
  2: now rewrite H.
  clear H; intro H.
  assert (Ø ∈ single Ø).
  now apply in_single.
  specialize (H (exist _ Ø H0)).
  simpl in H.
  apply eq_sig_fst in H.
  rewrite <- set_eq_ext in H.
  generalize (proj2 (H Ø) H0).
  apply in_empty.
Qed.

Lemma join_pi_id {C: ProdCategory} {a b: C}: ⟨π₁, π₂⟩ = @id C (a × b).
Proof.
  rewrite <- (join_pi (id C)).
  f_equiv.
  all: symmetry.
  all: apply comp_id_r.
Qed.

Lemma comp_join {C: ProdCategory} {a b c d: C} (f : b ~> c) (g: b ~> d) (h: a ~> b):
  ⟨f, g⟩ ∘ h = ⟨f ∘ h, g ∘ h⟩.
Proof.
  rewrite <- (join_pi _).
  f_equal.
  all: rewrite comp_assoc.
  now rewrite pi1_join.
  now rewrite pi2_join.
Qed.

Definition lift {C: ProdCategory} {a b c d: C} (f: a ~> c) (g: b ~> d): a × b ~> c × d :=
  ⟨f ∘ π₁, g ∘ π₂⟩.

Lemma lift_correct {C: ProdCategory} {a b c d e: C} (f: b ~> d) (g: c ~> e) (h1: a ~> b) (h2: a ~> c):
  lift f g ∘ ⟨h1, h2⟩ = ⟨f ∘ h1, g ∘ h2⟩.
Proof.
  unfold lift.
  rewrite comp_join.
  f_equiv.
  all: rewrite <- comp_assoc.
  all: f_equiv.
  apply pi1_join.
  apply pi2_join.
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
  apply join_pi_id.
Qed.

Lemma lift_comp {C: ProdCategory} {a1 a2 b1 b2 c1 c2: C} (f1: a1 ~> b1) (f2: a2 ~> b2) (g1: b1 ~> c1) (g2: b2 ~> c2):
  lift g1 g2 ∘ lift f1 f2 = lift (g1 ∘ f1) (g2 ∘ f2).
Proof.
  unfold lift.
  rewrite comp_join.
  f_equiv.
  all: rewrite <- !comp_assoc.
  all: f_equiv.
  apply pi1_join.
  apply pi2_join.
Qed.

End ex3.
