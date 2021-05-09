Require Export Topology.

Structure Sheaf (T: Topology) (C: SProdCategory) := {
  sobj: Topology.Open T -> C;
  smap {X Y: Topology.Open T}: Y ~> X -> sobj X ~> sobj Y;
  smap_id (X: Topology.Open T): smap (id X) = id (sobj X);
  smap_comp {Z Y X: Topology.Open T} (g: X ~> Y) (f: Y ~> Z): smap (f ∘ g) = smap g ∘ smap f;
  smap_cover {I} {X} {f: I -> Topology.Open T} (e: X ~> ∏ i, sobj (f i)):
    (forall i j, smap π₁ ∘ @π _ I (fun i => sobj (f i)) i ∘ e = smap π₂ ∘ @π _ I (fun i => sobj (f i)) j ∘ e) ->
    exists! u: X ~> sobj (scoprod f), ∏' i, smap (ι i) ∘ u = e;
}.

Arguments sobj {T C} s t.
Arguments smap {T C} s {X Y} f.
Arguments smap_id {T C} s X.
Arguments smap_comp {T C} s {Z Y X} g f.
Arguments smap_cover {T C} s {I X f} e.

Coercion sobj: Sheaf >-> Funclass.

Module Sheaf.

Structure hom {T: Topology} {C: SProdCategory} (F G: Sheaf T C) := Hom {
  strans X: F X ~> G X;
  snatural {X Y} (f: Y ~> X): strans Y ∘ smap F f = smap G f ∘ strans X;
}.

Arguments Hom {T C} F G strans snatural.
Arguments strans {T C F G} h X.
Arguments snatural {T C F G} h {X Y} f.
Coercion strans: hom >-> Funclass.

Lemma hom_eq {T: Topology} {C: SProdCategory} {F G: Sheaf T C} (η ϵ: hom F G): η = ϵ <-> forall x, η x = ϵ x.
Proof.
  split.
  now intros [].
  destruct η as [η Hη], ϵ as [ϵ Hϵ]; simpl.
  intros H.
  enough (η = ϵ); [subst ϵ|].
  f_equal; apply proof_irrelevance.
  now extensionality x.
Qed.

Program Definition cat_mixin (T: Topology) (C: SProdCategory) := Category.Mixin (Sheaf T C) hom
  (fun F => {|
    strans X := id (F X);
  |})
  (fun F G H η ϵ => {|
    strans X := η X ∘ ϵ X;
  |})
  _ _ _.
Next Obligation.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite snatural.
  rewrite !comp_assoc.
  f_equal.
  apply snatural.
Qed.
Next Obligation.
  apply hom_eq; simpl.
  intros X.
  apply comp_assoc.
Qed.
Next Obligation.
  apply hom_eq; simpl.
  intros X.
  apply comp_id_l.
Qed.
Next Obligation.
  apply hom_eq; simpl.
  intros X.
  apply comp_id_r.
Qed.

Canonical cat (T: Topology) (C: SProdCategory) := Category.Pack (Sheaf T C) (cat_mixin T C).

Program Definition sprodCat_mixin (T: Topology) (C: SProdCategory) := SProdCategory.Mixin (cat T C)
  (fun I F => {|
    sobj X := ∏ i, F i X;
    smap X Y f := (∏) i, smap (F i) f;
  |})
  (fun I F G f => {|
    strans X := ∏' i, f i X;
  |})
  (fun I F i => {|
    strans X := @π C I (fun i => F i X) i;
  |})
  _.
Next Obligation.
  setoid_rewrite smap_id.
  apply spmap_id.
Qed.
Next Obligation.
  setoid_rewrite smap_comp at 1.
  apply spmap_comp.
Qed.
Next Obligation.
  rename I0 into J.
  assert (forall i (j1 j2: J), smap (F i) π₁ ∘ π j1 ∘ ((∏) j, π i ∘ e) = smap (F i) π₂ ∘ π j2 ∘ ((∏) j, π i ∘ e)).
  1: {
    intros i j1 j2.
    specialize (H j1 j2).
    rewrite to_sprod_eq in H.
    specialize (H i).
    rewrite !comp_assoc in H.
    setoid_rewrite (pi_spmap _ i) in H.
    rewrite !comp_assoc.
    rewrite <- !(comp_assoc (smap (F i) _)).
    setoid_rewrite (pi_spmap _ j1).
    setoid_rewrite (pi_spmap _ j2).
    now rewrite !comp_assoc.
  }
  specialize (fun i => smap_cover (F i) _ (H0 i)).
  clear H H0.
  intros Hu.
  apply ex_unique_forall in Hu.
  destruct Hu as [u [Hu H1]].
  exists (sfork u); split.
  apply to_sprod_eq.
  intros j.
  rewrite comp_assoc.
  setoid_rewrite (pi_sfork _ j).
  rewrite spmap_sfork.
  apply to_sprod_eq.
  intros i.
  rewrite comp_assoc.
  setoid_rewrite (pi_sfork _ i).
  specialize (Hu i).
  rewrite to_sprod_eq in Hu.
  specialize (Hu j).
  rewrite !comp_assoc in Hu.
  setoid_rewrite (pi_sfork _ j) in Hu.
  exact Hu.
  intros g He.
  clear Hu.
  subst e.
  apply to_sprod_eq.
  intros i.
  rewrite (pi_sfork u).
  enough (u = fun i => π i ∘ g).
  now apply (f_equal (fun f => f i)) in H.
  clear i.
  apply H1; clear H1.
  intros i.
  rewrite !comp_assoc.
  f_equal.
  rewrite spmap_sfork.
  apply to_sprod_eq.
  intros j.
  rewrite !comp_assoc.
  setoid_rewrite (pi_sfork _ j).
  symmetry.
  exact (pi_spmap (fun i => smap (F i) (ι j)) i).
Qed.
Next Obligation.
  rewrite spmap_sfork.
  apply to_sprod_eq.
  intros i.
  rewrite comp_assoc.
  setoid_rewrite (pi_sfork _ i).
  apply snatural.
Qed.
Next Obligation.
  exact (pi_spmap (fun i => smap (F i) f) i).
Qed.
Next Obligation.
  setoid_rewrite hom_eq; simpl.
  now setoid_rewrite sfork_ump.
Qed.
Canonical sprodCat (T: Topology) (C: SProdCategory) := SProdCategory.Pack (cat T C) (sprodCat_mixin T C).

End Sheaf.

Coercion Sheaf.strans: Sheaf.hom >-> Funclass.
Canonical Sheaf.cat.

Canonical sf {T: Topology} {C: SProdCategory} (F: Sheaf T C) :=
  Build_Functor (co (Topology.Open T)) C
  F (@smap _ _ F)
  (smap_id F) (@smap_comp _ _ F).

Coercion sf: Sheaf >-> Functor.

Canonical sn {T: Topology} {C: SProdCategory} {F G: Sheaf T C} (η: F ~> G) :=
  Build_Natural _ _ (sf F) (sf G) η (@Sheaf.snatural T C F G η).

Program Canonical SF {T: Topology} {C: SProdCategory} := {|
  fobj := @sf T C;
  fmap := @sn T C;
|}.
Next Obligation.
  now natural_eq X.
Qed.
Next Obligation.
  now natural_eq X.
Qed.
