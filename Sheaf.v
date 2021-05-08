Require Export Topology.

Structure Sheaf (T: Topology) (C: SProdCategory) := {
  sobj: Topology.Open T -> C;
  smap {X Y: Topology.Open T}: Y ~> X -> sobj X ~> sobj Y;
  smap_id (X: Topology.Open T): smap (id X) = id (sobj X);
  smap_comp {Z Y X: Topology.Open T} (g: X ~> Y) (f: Y ~> Z): smap (f ∘ g) = smap g ∘ smap f;
  smap_cover {I} (f: I -> Topology.Open T) (e: sobj (scoprod f) ~> ∏ i, sobj (f i)):
    ∏' i, smap (ι i) = e <-> ((∏) i, ∏' j, smap π₁) ∘ e = (∏' i, (∏) j, smap π₂) ∘ e;
}.

Arguments sobj {T C} s t.
Arguments smap {T C} s {X Y} f.
Arguments smap_id {T C} s X.
Arguments smap_comp {T C} s {Z Y X} g f.
Arguments smap_cover {T C} s {I} f e.

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
