Require Export Limit.
Require Export Instances.Typ.
Require Export Categories.Two.
Require Export Categories.Meet.
Require Export Sets.Sets.

Definition is_pullback {C: Category} {S A B T: C} (f: A ~> T) (g: B ~> T) (p1: S ~> A) (p2: S ~> B) :=
  f ∘ p1 = g ∘ p2 /\
  forall (Z: C) (q1: Z ~> A) (q2: Z ~> B), f ∘ q1 = g ∘ q2 -> exists! u: Z ~> S, p1 ∘ u = q1 /\ p2 ∘ u = q2.

Definition is_pushout {C: Category} {S A B T: C} (f: S ~> A) (g: S ~> B) (i1: A ~> T) (i2: B ~> T) :=
  i1 ∘ f = i2 ∘ g /\
  forall (Z: C) (j1: A ~> Z) (j2: B ~> Z), j1 ∘ f = j2 ∘ g -> exists! u: T ~> Z, u ∘ i1 = j1 /\ u ∘ i2 = j2.

Definition is_equalizer {C: Category} {E A B: C} (f g: A ~> B) (e: E ~> A) :=
  f ∘ e = g ∘ e /\
  forall (Z: C) (d: Z ~> A), f ∘ d = g ∘ d -> exists! u: Z ~> E, e ∘ u = d.

Definition regular_monic {C: Category} {A B: C} (f: A ~> B) :=
  exists (X: C) (a b: B ~> X), is_equalizer a b f.

Lemma regular_monic_is_monic {C: Category} {A B: C} (f: A ~> B): regular_monic f -> monic f.
Proof.
  rename A into E, B into A, f into e.
  intros [B [f [g [H H0]]]] Z a b He.
  specialize (H0 Z (e ∘ b)).
  destruct H0 as [u [_ Hu]].
  rewrite !comp_assoc.
  now f_equal.
  transitivity u.
  symmetry.
  all: now apply Hu.
Qed.

Lemma is_pullback_sym {C: Category} {S A B T: C} (f: A ~> T) (g: B ~> T) (p1: S ~> A) (p2: S ~> B):
  is_pullback f g p1 p2 <-> is_pullback g f p2 p1.
Proof.
  revert S A B T f g p1 p2.
  enough (forall (S A B T: C) (f: A ~> T) (g: B ~> T) (p1: S ~> A) (p2: S ~> B), is_pullback f g p1 p2 -> is_pullback g f p2 p1).
  split; apply H.
  intros.
  split; [apply proj1 in H | apply proj2 in H].
  now symmetry.
  intros Z q2 q1 Hq.
  specialize (H Z q1 q2 (eq_sym Hq)).
  clear Hq.
  destruct H as [u H].
  exists u.
  split; [apply proj1 in H | apply proj2 in H].
  easy.
  intros u' Hu.
  now apply H.
Qed.

Section ex1.
Context {C: Category} {S A B T: C} (f: A ~> T) (g: B ~> T) (p1: S ~> A) (p2: S ~> B).
Context (pull: is_pullback f g p1 p2).

Lemma ex1_1: splitepic g -> splitepic p1.
Proof.
  intros [g' Hg].
  destruct pull.
  specialize (H0 A (id A) (g' ∘ f)).
  destruct H0 as [p1' [[H0 _] _]].
  rewrite comp_id_r, comp_assoc.
  rewrite Hg.
  symmetry.
  apply comp_id_l.
  now exists p1'.
Qed.

Lemma ex1_2': monic g -> monic p1.
Proof.
  intros Hg Z a b H.
  destruct pull; clear pull.
  specialize (H1 Z (p1 ∘ b) (p2 ∘ b)).
  destruct H1 as [u [_ Hu]].
  rewrite !comp_assoc.
  now f_equal.
  transitivity u.
  symmetry.
  all: apply Hu.
  split.
  exact H.
  apply Hg.
  rewrite !comp_assoc.
  rewrite <- H0.
  rewrite <- !comp_assoc.
  now f_equal.
  easy.
Qed.

Lemma ex1_2: is_iso g -> is_iso p1.
Proof.
  intros Hg.
  apply splitepic_monic.
  apply ex1_1, is_iso_is_splitepic, Hg.
  apply ex1_2', is_iso_monic, Hg.
Qed.

End ex1.

Lemma ex1_3: exists (C: Category) (S A B T: C) (f: A ~> T) (g: B ~> T) (p1: S ~> A) (p2: S ~> B), is_pullback f g p1 p2 /\ splitmonic f /\ ~splitmonic p1.
Proof.
  exists Typ, 0, 1, 1, bool.
  exists (fun _ => false), (fun _ => true).
  exists ¡, ¡.
  repeat split.
  + apply from_zero_eq.
  + intros Z q1 q2 H.
    assert (~inhabited Z) as Hz.
    intros [z].
    apply (f_equal (fun f => f z)) in H.
    discriminate H.
    assert (inhabited (Z ~> 0)).
    constructor.
    intros z.
    now destruct Hz.
    destruct H0 as [f].
    exists f.
    repeat split.
    3: intros g _.
    all: extensionality z.
    all: now destruct Hz.
  + exists !.
    apply to_one_eq.
  + intros [f H].
    destruct (f tt).
Qed.

Lemma ex2: exists (U: Category)
  (A B C D E F: U)
  (ab: A ~> B) (bc: B ~> C)
  (ad: A ~> D) (be: B ~> E) (cf: C ~> F)
  (de: D ~> E) (ef: E ~> F),
  is_pullback de be ad ab /\
  is_pullback (ef ∘ de) cf ad (bc ∘ ab) /\
  ~is_pullback ef cf be bc.
Proof.
  exists Typ.
  exists 1, 1, 1, 1, bool, 1.
  exists (id 1), (id 1).
  exists (id 1), (fun _ => true), (id 1).
  exists (fun _ => true), !.
  repeat split.
  + intros Z p1 p2 _.
    exists !.
    repeat split.
    3: intros f _.
    all: apply to_one_eq.
  + apply to_one_eq.
  + intros Z p1 p2 _.
    exists !.
    repeat split.
    3: intros f _.
    all: apply to_one_eq.
  + intros [_ H].
    specialize (H bool (id _) !).
    destruct H as [u [[H _] _]].
    etransitivity.
    symmetry.
    1, 2: apply to_one_unique.
    apply (f_equal (fun f => f false)) in H.
    discriminate H.
Qed.

Lemma ex3 {U: Category} {A C E E': U} (h: C ~> A) (e: E ~> A) (e': E' ~> C) (p: E' ~> E): is_pullback h e e' p -> regular_monic e -> regular_monic e'.
Proof.
  intros [HP Hp] [B [f [g [He H]]]].
  exists B, (f ∘ h), (g ∘ h).
  split.
  rewrite <- !comp_assoc.
  rewrite HP.
  rewrite !comp_assoc.
  now f_equal.
  intros Z d Hd.
  specialize (H Z (h ∘ d)).
  rewrite !comp_assoc in H.
  specialize (H Hd).
  destruct H as [u Hu].
  specialize (Hp Z d u).
  destruct Hp as [v [[Hv1 Hv2] Hv]].
  symmetry.
  apply Hu.
  subst d u.
  exists v.
  split.
  reflexivity.
  intros v' Hv'.
  apply Hv.
  split.
  exact Hv'.
  symmetry.
  apply Hu.
  rewrite <- Hv'.
  rewrite !comp_assoc.
  now f_equal.
Qed.

Lemma ex_4 {U: Category} {A B Q: U} (x y: B ~> Q) (e: A ~> B): regular_monic e -> is_pushout e e x y -> is_equalizer x y e.
Proof.
  intros [C [f [g [H He]]]] [H0 Hp].
  split.
  exact H0.
  specialize (Hp C f g H).
  intros Z d Hd.
  apply He; clear He.
  destruct Hp as [q [[H1 H2] Hq]].
  subst f g.
  rewrite <- !comp_assoc.
  now f_equal.
Qed.

Section test.
Local Obligation Tactic := idtac.
Program Definition square_nat {U: Category} {A B C D: U} (f: B ~> D) (g: C ~> D) (p1: A ~> B) (p2: A ~> C) (H: f ∘ p1 = g ∘ p2): Δ A ~> Meet.F f g := {|
  transform x :=
    match x return A ~> Meet.choose B C D x with
    | Meet.left => p1
    | Meet.right => p2
    | Meet.center => g ∘ p2
    end;
|}.
Next Obligation.
  intros.
  destruct f0.
  subst y.
  destruct x; simpl.
  1, 2, 3: rewrite comp_id_l.
  1, 2, 3: apply comp_id_r.
  destruct a.
  subst y.
  destruct o; subst x; simpl.
  all: rewrite comp_id_r.
  now symmetry.
  reflexivity.
Qed.
End test.

Lemma pullback_limit {U: Category} {A B C D: U} (f: B ~> D) (g: C ~> D) (p1: A ~> B) (p2: A ~> C):
  is_pullback f g p1 p2 <-> f ∘ p1 = g ∘ p2 /\ forall e: f ∘ p1 = g ∘ p2, is_limit' _ A (square_nat f g p1 p2 e).
Proof.
  split.
  + intros [H Hp].
    split.
    exact H.
    clear H.
    intros H n ϵ.
    assert (f ∘ ϵ Meet.left = g ∘ ϵ Meet.right) as Hϵ.
    etransitivity.
    symmetry.
    exact (naturality ϵ Meet.inl).
    exact (naturality ϵ Meet.inr).
    specialize (Hp n (ϵ Meet.left) (ϵ Meet.right) Hϵ).
    destruct Hp as [u Hu].
    exists u.
    split; [apply proj1 in Hu | apply proj2 in Hu].
    natural_eq x.
    destruct x.
    1, 2: apply Hu.
    rewrite <- comp_id_r.
    setoid_rewrite (naturality ϵ Meet.inr).
    rewrite <- comp_assoc.
    now f_equal.
    intros u' Hu'.
    generalize (proj1 (natural_eq _ _) Hu').
    clear Hu'; intros Hu'.
    apply Hu.
    split.
    exact (Hu' Meet.left).
    exact (Hu' Meet.right).
  + intros [H HL].
    specialize (HL H).
    split.
    exact H.
    intros Z q1 q2 Hq.
    specialize (HL Z (square_nat f g q1 q2 Hq)).
    destruct HL as [u Hu].
    exists u.
    split; [apply proj1 in Hu | apply proj2 in Hu].
    generalize (proj1 (natural_eq _ _) Hu).
    clear Hu; intros Hu.
    repeat split.
    exact (Hu Meet.left).
    exact (Hu Meet.right).
    intros u' [H1 H2].
    apply Hu.
    natural_eq x.
    destruct x.
    1, 2: assumption.
    rewrite <- comp_assoc.
    now f_equal.
Qed.

Lemma mono_as_pullback {C: Category} {a b: C} (f: a ~> b): monic f <-> is_pullback f f (id a) (id a).
Proof.
  split.
  + intros Hf.
    split.
    reflexivity.
    intros Z p1 p2 H.
    apply Hf in H.
    subst p2.
    exists p1.
    repeat split.
    1, 2: apply comp_id_l.
    intros u [Hu _].
    rewrite comp_id_l in Hu.
    now symmetry.
  + intros [_ Hf] Z g1 g2 H.
    specialize (Hf Z g1 g2 H).
    destruct Hf as [u [[Hu1 Hu2] _]].
    rewrite comp_id_l in Hu1, Hu2.
    now transitivity u.
Qed.

Lemma Meet_fin: fin Meet.
Proof.
  split.
  exists (Meet.left :: Meet.right :: Meet.center :: nil)%list.
  intros []; do 3 [> now left | right..].
  intros [] [].
  2, 4, 7, 8: exists nil.
  1: exists (id Meet.left :: nil)%list.
  7: exists (id Meet.right :: nil)%list.
  9: exists (id Meet.center :: nil)%list.
  6: exists (Meet.inl :: nil)%list.
  8: exists (Meet.inr :: nil)%list.
  all: intros x.
  1, 6, 7, 8, 9: left.
  1, 2, 3, 4, 5: unfold hom; simpl.
  1, 2, 3, 4, 5: apply proof_irrelevance.
  all: simpl.
  all: destruct x.
  all: try apply proj2 in H.
  all: discriminate H.
Qed.

Lemma comp_meet_F {S T: Category} {x y z: S} (F: S ~> T) (f: x ~> z) (g: y ~> z): F ∘ Meet.F f g = Meet.F (fmap F f) (fmap F g).
Proof.
  fun_eq a b e.
  now destruct x0.
  destruct e.
  + subst b.
    destruct a; simpl in H, H0.
    all: rewrite !eq_iso_refl.
    all: f_equal.
    all: apply fmap_id.
  + destruct a0.
    subst b.
    destruct o; subst a.
    all: simpl in H, H0.
    all: rewrite !eq_iso_refl.
    all: simpl.
    all: rewrite comp_id_r.
    all: apply comp_id_l.
Qed.

Lemma ex_5 {C D: Category} {x y: C} (F: C ~> D) (f: x ~> y): fin_continue F -> monic f -> monic (fmap F f).
Proof.
  rewrite !mono_as_pullback.
  rewrite !pullback_limit.
  intros HF [_ HL].
  specialize (HF Meet Meet_fin).
  specialize (HL eq_refl).
  rewrite preserve_alt in HF.
  apply HF in HL; clear HF.
  split.
  reflexivity.
  intros e.
  intros n ϵ.
  specialize (HL n ((eq_iso (comp_meet_F F f f))⁻¹ ∘ ϵ)).
  destruct HL as [u Hu].
  exists u.
  split; [apply proj1 in Hu | apply proj2 in Hu].
  + generalize (proj1 (natural_eq _ _) Hu).
    clear Hu; intros Hu.
    natural_eq a.
    specialize (Hu a).
    destruct a; simpl in Hu |- *.
    1, 2: rewrite fmap_id, comp_id_l in Hu.
    1, 2: rewrite comp_id_l.
    setoid_rewrite (is_eq_refl (to (eq_iso (comp_diag F x))⁻¹ Meet.left)) in Hu.
    setoid_rewrite (is_eq_refl (to (eq_iso (comp_meet_F F f f))⁻¹ Meet.left)) in Hu.
    now rewrite !comp_id_l in Hu.
    apply (transform_is_eq (eq_iso (comp_meet_F F f f))⁻¹), is_eq_inv, eq_iso_is_eq.
    apply (transform_is_eq (eq_iso (comp_diag F x))⁻¹), is_eq_inv, eq_iso_is_eq.
    setoid_rewrite (is_eq_refl (to (eq_iso (comp_diag F x))⁻¹ Meet.right)) in Hu.
    setoid_rewrite (is_eq_refl (to (eq_iso (comp_meet_F F f f))⁻¹ Meet.right)) in Hu.
    now rewrite !comp_id_l in Hu.
    apply (transform_is_eq (eq_iso (comp_meet_F F f f))⁻¹), is_eq_inv, eq_iso_is_eq.
    apply (transform_is_eq (eq_iso (comp_diag F x))⁻¹), is_eq_inv, eq_iso_is_eq.
    rewrite fmap_comp, fmap_id, comp_id_r in Hu.
    rewrite comp_id_r.
    setoid_rewrite (is_eq_refl (to (eq_iso (comp_diag F x))⁻¹ Meet.center)) in Hu.
    setoid_rewrite (is_eq_refl (to (eq_iso (comp_meet_F F f f))⁻¹ Meet.center)) in Hu.
    now rewrite comp_id_r, comp_id_l in Hu.
    apply (transform_is_eq (eq_iso (comp_meet_F F f f))⁻¹), is_eq_inv, eq_iso_is_eq.
    apply (transform_is_eq (eq_iso (comp_diag F x))⁻¹), is_eq_inv, eq_iso_is_eq.
  + intros u' Hu'.
    generalize (proj1 (natural_eq _ _) Hu').
    clear Hu'; intros Hu'.
    apply Hu; clear Hu.
    natural_eq a.
    specialize (Hu' a).
    destruct a; simpl in Hu' |- *.
    1, 2: rewrite comp_id_l in Hu'.
    3: rewrite comp_id_r in Hu'.
    1, 2: rewrite fmap_id, comp_id_l.
    3: rewrite comp_id_r.
    1, 2: subst u'; f_equal.
    1, 2: apply is_eq_unique.
    1, 3: apply (transform_is_eq (eq_iso (comp_diag F x))⁻¹).
    3: apply (transform_is_eq (eq_iso (comp_meet_F F f f))⁻¹ Meet.left).
    4: apply (transform_is_eq (eq_iso (comp_meet_F F f f))⁻¹ Meet.right).
    1, 2, 3, 4: apply is_eq_inv, eq_iso_is_eq.
    rewrite <- Hu'.
    rewrite comp_assoc.
    f_equal.
    etransitivity.
    etransitivity.
    apply f_equal.
    3: apply (f_equal (fun f => f ∘ _)).
    3: symmetry.
    1, 3: apply is_eq_refl.
    1: apply (transform_is_eq (eq_iso (comp_diag F x))⁻¹).
    2: apply (transform_is_eq (eq_iso (comp_meet_F F f f))⁻¹ Meet.center).
    1, 2: apply is_eq_inv, eq_iso_is_eq.
    rewrite comp_id_l.
    apply comp_id_r.
Qed.

Lemma ex_6_1: exists F: SET ~> SET, preserve F ZERO /\ create F ZERO.
Proof.
  exists (id SET).
  split.
  + apply preserve_alt.
    intros G l η HL n ϵ.
    specialize (HL n (λ G ∘ ϵ)).
    destruct HL as [u Hu].
    exists u.
    split; [apply proj1 in Hu | apply proj2 in Hu].
    now natural_eq x.
    intros u' Hu'.
    apply Hu.
    now natural_eq x.
  + intros G L HL.
    assert (exists l η, cone_nat l η = L).
    exists (Cone.vertex L), (nat_cone L).
    apply nat_cone_inv.
    destruct H as [l [η]].
    subst L.
    rewrite <- is_limit_alt' in HL.
    exists (cone_nat l (λ G ∘ η)).
    repeat split.
    rewrite <- (nat_cone_inv (cone_whisk_l _ _ _)).
    f_equal.
    natural_eq x.
    apply comp_id_l.
    intros L H.
    assert (exists l η, cone_nat l η = L).
    exists (Cone.vertex L), (nat_cone L).
    apply nat_cone_inv.
    destruct H0 as [l' [η']].
    subst L.
    specialize (f_equal Cone.vertex H) as Hl.
    simpl in Hl.
    subst l'.
    f_equal.
    now natural_eq x.
    rewrite <- is_limit_alt'.
    intros n ϵ.
    specialize (HL n ((λ G)⁻¹ ∘ ϵ)).
    destruct HL as [u Hu].
    exists u.
    split; [apply proj1 in Hu | apply proj2 in Hu].
    apply (iso_monic (λ G)⁻¹).
    rewrite !comp_assoc, inv_l, (comp_id_l η).
    exact Hu.
    intros f Hf.
    apply Hu.
    apply (iso_monic (λ G)).
    rewrite !comp_assoc, inv_r, comp_id_l.
    exact Hf.
Qed.

Lemma ex_6_2: exists F: SET ~> SET, preserve F ZERO /\ ~create F ZERO.
Proof.
  exists (Δ 1).
  split.
  + apply preserve_alt.
    intros G l η HL n ϵ.
    exists !.
    split.
    now natural_eq x.
    intros f H.
    apply to_one_unique.
  + unshelve refine (fun H => let H := (H (Δ 1) (cone_nat 1 _)) in _).
    apply ((eq_iso (diag_comp 1 (Δ 1)))⁻¹).
    clearbody H; clear H0.
    destruct H as [L H].
    rewrite <- is_limit_alt'.
    intros n η.
    exists !.
    split.
    now natural_eq x.
    intros f _.
    apply to_one_unique.
    destruct H as [[_ H] _].
    absurd (@cone_nat ZERO SET (Δ 1) 1 (id _) = @cone_nat ZERO SET (Δ 1) 0 (fmap Δ !)).
    intros e.
    apply (f_equal Cone.vertex) in e.
    simpl in e.
    eapply single_not_empty, e.
    transitivity L.
    symmetry.
    all: apply H; clear H.
    all: now apply Cone.obj_eq.
Qed.

Lemma ex_6_3: exists F: SET ~> SET, ~preserve F ZERO /\ ~create F ZERO.
Proof.
  exists (Δ 0).
  split.
  + intros H.
    rewrite preserve_alt in H.
    specialize (H (Δ 0) 1).
    assert (@Δ SET ZERO 1 ~> Δ 0) as η.
    exists (Empty_set_rect _).
    intros x.
    destruct x.
    assert (is_limit' _ _ η).
    intros n ϵ.
    exists !.
    split.
    now natural_eq x.
    intros f _.
    apply to_one_unique.
    specialize (H η H0 1).
    assert (@Δ SET ZERO 1 ~> @Δ SET SET 0 ∘ Δ 0) as ϵ.
    exists (Empty_set_rect _).
    intros x.
    destruct x.
    specialize (H ϵ).
    destruct H as [f _].
    apply (in_empty (map f Ø)).
    now apply mapto, in_single.
  + intros H.
    assert (@Δ SET ZERO 1 ~> @Δ SET SET 0 ∘ Δ 0) as η.
    exists (Empty_set_rect _).
    intros x.
    destruct x.
    specialize (H (Δ 0) (cone_nat 1 η)).
    destruct H as [L [[HL _] _]].
    rewrite <- is_limit_alt'.
    intros n ϵ.
    exists !.
    split.
    now natural_eq x.
    intros f _.
    apply to_one_unique.
    apply (f_equal Cone.vertex) in HL.
    simpl in HL.
    now apply (single_not_empty Ø).
Qed.

Lemma ex_6_4 (F: SET ~> SET): create F ZERO -> preserve F ZERO.
Proof.
  intros H G L HL.
  assert (Δ 1 ~> F ∘ G) as η.
  exists (Empty_set_rect _).
  exact (Empty_set_rect _).
  specialize (H G (cone_nat 1 η)).
  destruct H as [L' [[H _] HL']].
  rewrite <- is_limit_alt'.
  intros l ϵ.
  exists !.
  split.
  now natural_eq x.
  intros f _.
  apply to_one_unique.
  assert (L ≃ L').
  now apply iso_limit.
  rewrite H0.
  rewrite H.
  rewrite <- is_limit_alt'.
  intros n ϵ.
  exists !.
  split.
  now natural_eq x.
  intros f _.
  apply to_one_unique.
Qed.

Lemma ex_7_1: exists (S T: Category) (F: S ~> T) (x y: S) (f: x ~> y), monic f /\ ~monic (fmap F f).
Proof.
  exists 2, Typ.
  unshelve eexists.
  2: exists false, true, tt.
  2: split.
  unshelve eexists.
  intros [].
  exact 1.
  exact bool.
  intros [] [].
  1, 4: exact (fun _ => id _).
  apply Empty_set_rect.
  exact (fun _ => !).
  4: simpl.
  now intros [].
  intros [] [] [] [] [].
  1, 2, 3: apply to_one_eq.
  symmetry.
  apply comp_id_l.
  now intros [] [] [].
  intros H.
  absurd ((fun _: unit => false) = (fun _ => true)).
  intros e.
  apply (f_equal (fun f => f tt)) in e.
  discriminate e.
  apply H; clear H.
  apply to_one_eq.
Qed.

Lemma ex_7_2: exists (S T: Category) (F: S ~> T) (x y: S) (f: x ~> y), epic f /\ ~epic (fmap F f).
Proof.
  exists 2, Typ.
  unshelve eexists.
  2: exists false, true, tt.
  2: split.
  unshelve eexists.
  intros [].
  exact bool.
  exact 1.
  intros [] [].
  1, 4: exact (fun _ => id _).
  apply Empty_set_rect.
  exact (fun _ _ => true).
  4: simpl.
  now intros [].
  now intros [] [] [] [] [].
  now intros [] [] [].
  intros H.
  red in H.
  absurd ((andb true) = (orb true)).
  intros e.
  apply (f_equal (fun f => f false)) in e.
  discriminate e.
  now apply H.
Qed.