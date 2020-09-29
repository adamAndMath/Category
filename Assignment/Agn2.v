Require Export Categories.Parallel.
Require Export Categories.Poset.
Require Export Categories.Slice.
Require Export Limit.
Require Export Limits.Product.
Require Export Limits.Coproduct.

Section ex1.
Context {T: Type}.

Lemma poset_equalizer (R: T -> T -> Prop) {pre: PreOrder R} (po: PartialOrder eq R): has_limit Parallel (Poset R).
Proof.
  intros F.
  unshelve eexists.
  unshelve econstructor.
  exact (F false).
  intros [].
  exact (fmap F (Parallel.arr false)).
  exact (id (F false)).
  intros x y f.
  apply Proset.hom_eq.
  intros N.
  unshelve eexists.
  exists (Cone.edge N false).
  simpl.
  intros x.
  apply Proset.hom_eq.
  intros [f Hf].
  simpl in f, Hf.
  Cone.hom_eq.
  apply Proset.hom_eq.
Qed.

Lemma poset_coequalizer (R: T -> T -> Prop) {pre: PreOrder R} (po: PartialOrder eq R): has_colimit Parallel (Poset R).
Proof.
  apply has_limit_co.
  rewrite dual_poset.
  generalize (@poset_equalizer (flip R) _ (PartialOrder_inverse po)).
  apply has_limit_iso.
  symmetry.
  exact Parallel.dual_iso.
  reflexivity.
Qed.

End ex1.

Section ex2.

Lemma iso_prod (C D: Category): C ≃ D -> inhabited (ProdCategory.mixin_of C) <-> inhabited (ProdCategory.mixin_of D).
Proof.
  intros H.
  rewrite <- !prod_limit.
  now f_equiv.
Qed.

Lemma iso_coprod (C D: Category): C ≃ D -> inhabited (CoprodCategory.mixin_of C) <-> inhabited (CoprodCategory.mixin_of D).
Proof.
  intros H.
  rewrite <- !coprod_limit.
  rewrite <- !ex_lim_co.
  now do 2 f_equiv.
Qed.

Lemma iso_equalizer (C D: Category): C ≃ D -> has_limit Parallel C <-> has_limit Parallel D.
Proof.
  intros H.
  now f_equiv.
Qed.

Lemma iso_coequalizer (C D: Category): C ≃ D -> has_colimit Parallel C <-> has_colimit Parallel D.
Proof.
  intros H.
  rewrite <- !has_limit_co.
  rewrite <- Parallel.dual_iso.
  now do 2 f_equiv.
Qed.

End ex2.

Section ex3_1.
Context (C: Category) (X: C).

Definition slice_one: C / X := {|
  Slice.dom := X;
  Slice.oarr := id X;
|}.

Definition slice_to_one (a: C / X): a ~> slice_one := {|
  Slice.arr := Slice.oarr a: Slice.dom a ~> Slice.dom slice_one;
  Slice.comm := comp_id_l (Slice.oarr a);
|}.

Lemma slice_to_one_unique (a: C / X) (f: a ~> slice_one): slice_to_one a = f.
Proof.
  apply Slice.hom_eq; simpl.
  specialize (Slice.comm f) as H.
  simpl in H.
  rewrite comp_id_l in H.
  now symmetry.
Qed.

Definition TopSlice_mixin: TopCategory.mixin_of (C / X) :=
  TopCategory.Mixin (C / X) slice_one slice_to_one slice_to_one_unique.

Definition TopSlice: TopCategory :=
  TopCategory.Pack (C / X) TopSlice_mixin.

End ex3_1.

Section ex3_2.
Context (C: BotCategory) (X: C).

Definition slice_zero: C / X := {|
  Slice.dom := 0;
  Slice.oarr := from_zero;
|}.

Definition slice_from_zero (a: C / X): slice_zero ~> a := {|
  Slice.arr := from_zero: Slice.dom slice_zero ~> Slice.dom a;
  Slice.comm := eq_sym (from_zero_unique _);
|}.

Lemma slice_from_zero_unique (a: C / X) (f: slice_zero ~> a): slice_from_zero a = f.
Proof.
  apply Slice.hom_eq; simpl.
  apply from_zero_unique.
Qed.

Definition BotSlice_mixin: BotCategory.mixin_of (C / X) :=
  BotCategory.Mixin (C / X) slice_zero slice_from_zero slice_from_zero_unique.

Definition BotSlice: BotCategory :=
  BotCategory.Pack (C / X) BotSlice_mixin.

End ex3_2.

Section ex3_3.

Program Definition slice_parallel_cone {C: Category} {X: C} (F: Parallel ~> C / X) (x: Cone (Slice.Dom C X ∘ F)): Cone F := {|
  Cone.vertex := {|
    Slice.dom := Cone.vertex x;
    Slice.oarr := Slice.oarr (F false) ∘ Cone.edge x false;
  |};
  Cone.edge i := {|
    Slice.arr := Cone.edge x i;
  |};
|}.
Next Obligation.
  destruct i.
  2: reflexivity.
  rewrite <- (Cone.edge_comm x (Parallel.arr false)).
  simpl.
  rewrite comp_assoc.
  f_equal.
  apply Slice.comm.
Qed.
Next Obligation.
  apply Slice.hom_eq; simpl.
  exact (Cone.edge_comm x f).
Qed.

Program Definition parallel_cone_slice {C: Category} {X: C} (F: Parallel ~> C / X) (x: Cone F): Cone (Slice.Dom C X ∘ F) := {|
  Cone.vertex := Slice.dom (Cone.vertex x);
  Cone.edge i := Slice.arr (Cone.edge x i);
|}.
Next Obligation.
  change (Slice.arr (fmap F f ∘ Cone.edge x x0) = Slice.arr (Cone.edge x y)).
  f_equal.
  apply Cone.edge_comm.
Qed.

Program Definition parallel_conemor_slice {C: Category} {X: C} {F: Parallel ~> C / X} {x y: Cone F} (f: x ~> y): parallel_cone_slice F x ~> parallel_cone_slice F y := {|
  Cone.mediator := Slice.arr (Cone.mediator f);
|}.
Next Obligation.
  change (Slice.arr (Cone.edge y x0 ∘ f) = Slice.arr (Cone.edge x x0)).
  f_equal.
  apply Cone.mediator_comm.
Qed.

Lemma ex_parallel_cone_slice {C: Category} {X: C} (F: Parallel ~> C / X) (x: Cone (Slice.Dom C X ∘ F)): exists x': Cone F, parallel_cone_slice F x' = x.
Proof.
  exists (slice_parallel_cone F x).
  destruct x.
  unfold parallel_cone_slice, slice_parallel_cone;
  simpl.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma ex_slice_parallel_cone {C: Category} {X: C} (F: Parallel ~> C / X) (x: Cone F): exists x': Cone (Slice.Dom C X ∘ F), slice_parallel_cone F x' = x.
Proof.
  exists (parallel_cone_slice F x).
  destruct x.
  unfold parallel_cone_slice, slice_parallel_cone;
  simpl.
  set (v' := {|
    Slice.dom := Slice.dom vertex;
    Slice.oarr := Slice.oarr (F false) ∘ Slice.arr (edge false)
  |}).
  set (ec := slice_parallel_cone_obligation_1 C X F {|
    Cone.vertex := Slice.dom vertex;
    Cone.edge := fun i0 : Parallel => Slice.arr (edge i0): Slice.dom vertex ~> (Slice.Dom C X ∘ F) i0;
    Cone.edge_comm := parallel_cone_slice_obligation_1 C X F
                 {|
                 Cone.vertex := vertex;
                 Cone.edge := edge;
                 Cone.edge_comm := edge_comm |} |}:
    forall i: Parallel, Slice.oarr (F i) ∘ Slice.arr (edge i) = Slice.oarr v'
  ).
  change (slice_parallel_cone_obligation_1 _ _ _ _ ?i) with (ec i).
  set (e := fun i : Parallel => {| Slice.arr := Slice.arr (edge i); Slice.comm := ec i |}).
  clearbody e.
  simpl in e.
  set (slice_parallel_cone_obligation_2 C X F
  {|
  vertex := Slice.dom vertex;
  edge := fun i : Parallel => Slice.arr (edge i): Slice.dom vertex ~> (Slice.Dom C X ∘ F) i;
  edge_comm := parallel_cone_slice_obligation_1 C X F
                 {|
                 vertex := vertex;
                 edge := edge;
                 edge_comm := edge_comm |} |}).
  assert (vertex = {|
  Slice.dom := Slice.dom vertex;
  Slice.oarr := Slice.oarr (F false) ∘ Slice.arr (edge false) |}).
  destruct vertex; simpl.
  f_equal.
  symmetry.
  apply (Slice.comm (edge false)).
  rewrite <- H.
  specialize (edge_comm false true).
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma is_slice_equalizer (C: Category) (X: C) (F: Parallel ~> C / X): ex_limit (Slice.Dom C X ∘ F) -> ex_limit F.
Proof.
  intros [L' H].
  destruct (ex_parallel_cone_slice F L') as [L HL].
  subst L'.
  exists L.
  intros N.
  specialize (H (parallel_cone_slice F N)).
  destruct H as [f Hf].
  unshelve eexists.
  unshelve eexists.
  3: intros g.
  3: conemor_eq.
  unshelve eexists.
  3: intros b.
  3, 4: apply Slice.hom_eq; simpl.
  exact f.
  set (mediator_comm f).
  simpl.
  rewrite <- comp_assoc.
  etransitivity.
  apply f_equal.
  apply (mediator_comm f false).
  apply Slice.comm.
  apply (mediator_comm f b).
  assert (forall x : Parallel, edge L x ∘ Slice.arr (mediator g) = Slice.arr (edge N x)).
  intros x.
  set (@Slice.comm).
  set (Build_ConeMor _ _ _ (parallel_cone_slice F N) L (Slice.arr (mediator g))).
  simpl in c.
  set (Slice.arr (mediator g)).
  simpl in h.
  set (c (mediator g)).
  specialize (fun g => f_equal mediator (Hf g)).
  clear Hf; intros Hf.
  eapply Hf.
  set (g' := {| mediator := g |}: parallel_cone_slice F N ~> L).
  eapply Hf.

Lemma slice_equalizer (C: Category) (X: C): has_limit Parallel C -> has_limit Parallel (C / X).
Proof.
  intros Hl F.
  specialize (Hl (Slice.Dom C X ∘ F)).
  apply ex_limit_alt in Hl.
  apply ex_limit_alt.
  destruct Hl as [l [η Hl]].
  unshelve eexists.
  unshelve eexists.
  exact l.
  exact (Slice.oarr (F false) ∘ η false).
  unshelve eexists.
  unshelve eexists.
  intros [].
  1, 2: unshelve econstructor.
  1, 2: simpl.
  exact (η true).
  exact (η false).
  1, 2: simpl.
  2: reflexivity.
  etransitivity.
  2: apply (f_equal (fun f => f ∘ _)).
  2: apply (Slice.comm (fmap F (Parallel.arr false))).
  etransitivity.
  2: apply comp_assoc.
  f_equal.
  etransitivity.
  symmetry.
  apply comp_id_r.
  apply (naturality η (Parallel.arr false)).
  intros [] [] [].
  1, 2, 3, 4: apply Slice.hom_eq; simpl.
  1, 2, 3, 4: apply (naturality η).
  intros n ϵ.
  specialize ()
  all: simpl.
  simpl in h.
Qed.
End ex3_3.
