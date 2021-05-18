Require Export Instances.Typ.
Require Export Categories.Presheave.

Program Definition PresheaveSProd_mixin C := SProdCategory.Mixin (Presheave.cat C)
  (fun I F => {|
    pobj X := forall i, F i X;
    pmap X Y f x i := pmap (F i) f (x i);
  |})
  (fun I P F f => {|
    ptrans X x i := f i X x;
  |})
  (fun I F i => {|
    ptrans X f := f i;
  |})
  _.
Next Obligation.
  extensionality i.
  apply pmap_id.
Qed.
Next Obligation.
  extensionality i.
  apply pmap_comp.
Qed.
Next Obligation.
  extensionality i.
  apply pnatural.
Qed.
Next Obligation.
  split.
  + intros H.
    subst g.
    intros i.
    now apply Presheave.hom_eq.
  + intros H.
    apply Presheave.hom_eq; simpl.
    intros Z z.
    extensionality i.
    specialize (H i).
    now apply (f_equal (fun f: X ~> _ => f Z z)) in H.
Qed.

Canonical PresheaveSProd C := SProdCategory.Pack (Presheave.cat C) (PresheaveSProd_mixin C).

Program Definition PresheaveSCoprod_mixin C := SCoprodCategory.Mixin (Presheave.cat C)
  (fun I F => {|
    pobj X := { i & F i X };
    pmap X Y f x := existT _ (projT1 x) (pmap (F (projT1 x)) f (projT2 x));
  |})
  (fun I P F f => {|
    ptrans X x := f (projT1 x) X (projT2 x);
  |})
  (fun I F i => {|
    ptrans X x := existT _ i x;
  |})
  _.
Next Obligation.
  f_equal; simpl.
  apply pmap_id.
Qed.
Next Obligation.
  f_equal; simpl.
  apply pmap_comp.
Qed.
Next Obligation.
  f_equal; simpl.
  apply pnatural.
Qed.
Next Obligation.
  split.
  + intros H.
    subst g.
    intros i.
    now apply Presheave.hom_eq.
  + intros H.
    apply Presheave.hom_eq; simpl.
    intros Z [i z]; simpl.
    specialize (H i).
    now apply (f_equal (fun f: _ ~> X => f Z z)) in H.
Qed.

Canonical PresheaveSCoprod C := SCoprodCategory.Pack (Presheave.cat C) (PresheaveSCoprod_mixin C).

Program Definition PFix {C D: Category} (F: Functor D (Presheave.cat C)) (X: C): Functor D Typ := {|
  fobj Y := F Y X;
  fmap Y Z f := fmap F f X;
  |}.
Next Obligation.
  now rewrite fmap_id.
Qed.
Next Obligation.
  now rewrite fmap_comp.
Qed.

Program Definition PresheaveComp_mixin C := Complete.Mixin (Presheave.cat C)
  (fun D F => {|
    pobj X := lim (PFix F X);
    pmap X Y f := @Lim_map _ D (PFix F X) (PFix F Y) {|
      transform Z := fmap (F Z) f;
    |};
  |})
  (fun D F => {|
    transform X := {|
      ptrans Y := Lim (PFix F Y) X;
    |}
  |})
  (fun D F P η => {|
    ptrans X := @lim_med TypComp D (PFix F X) (P X) {|
      transform Y := η Y X;
    |};
  |}) _ _.
Next Obligation.
  extensionality e.
  symmetry.
  apply pnatural.
Qed.
Next Obligation.
  apply TypComp.obj_eq; simpl.
  intros i.
  unfold comp; simpl.
  apply pmap_id.
Qed.
Next Obligation.
  apply TypComp.obj_eq; simpl.
  unfold comp at 1 3; simpl.
  intros i.
  apply pmap_comp.
Qed.
Next Obligation.
  rewrite comp_id_r.
  apply Presheave.hom_eq; simpl.
  rename x into X, y into Y.
  intros Z z.
  symmetry.
  change ((fmap (PFix F Z) f ∘ Lim (PFix F Z) X) z = Lim (PFix F Z) Y z).
  apply (f_equal (fun f => f z)); clear z.
  rewrite <- naturality.
  apply (comp_id_r (Lim (PFix F Z) Y)).
Qed.
Next Obligation.
  change ((η y ∘ (id P)) X = (fmap F f ∘ η x) X).
  f_equal.
  apply (naturality η).
Qed.
Next Obligation.
  apply TypComp.obj_eq; simpl.
  intros i.
  apply pnatural.
Qed.
Next Obligation.
  natural_eq Y.
  now apply Presheave.hom_eq.
Qed.
Next Obligation.
  apply Presheave.hom_eq; simpl.
  intros Y x.
  now apply TypComp.obj_eq.
Qed.

Canonical PresheaveComp C := Complete.Pack (Presheave.cat C) (PresheaveComp_mixin C).

Program Definition PresheaveCocomp_mixin C := Cocomplete.Mixin (Presheave.cat C)
  (fun D F => {|
    pobj X := colim (PFix F X);
    pmap X Y f := @Colim_map _ D (PFix F X) (PFix F Y) {|
      transform Z := fmap (F Z) f;
    |};
  |})
  (fun D F => {|
    transform X := {|
      ptrans Y := Colim (PFix F Y) X;
    |}
  |})
  (fun D F P η => {|
    ptrans X := @colim_med TypCocomp D (PFix F X) (P X) {|
      transform Y := η Y X;
    |};
  |}) _ _.
Next Obligation.
  extensionality e.
  symmetry.
  apply pnatural.
Qed.
Next Obligation.
  destruct (TypCocomp.Obj_surj x) as [Y [y H]].
  subst x.
  rewrite Colim_map_TypObj; simpl.
  f_equal.
  apply pmap_id.
Qed.
Next Obligation.
  destruct (TypCocomp.Obj_surj x) as [y [y' H]].
  subst x.
  rewrite !Colim_map_TypObj; simpl.
  f_equal.
  apply pmap_comp.
Qed.
Next Obligation.
  symmetry.
  apply Colim_map_TypObj.
Qed.
Next Obligation.
  rewrite comp_id_l.
  apply Presheave.hom_eq; simpl.
  rename x into X, y into Y.
  intros Z z.
  change ((Colim (PFix F Z) Y ∘ fmap (PFix F Z) f) z = Colim (PFix F Z) X z).
  apply (f_equal (fun f => f z)); clear z.
  rewrite naturality.
  apply (comp_id_l (Colim (PFix F Z) X)).
Qed.
Next Obligation.
  rewrite comp_id_l.
  change ((η y ∘ fmap F f) X = η x X).
  f_equal.
  rewrite naturality; simpl.
  apply comp_id_l.
Qed.
Next Obligation.
  destruct (TypCocomp.Obj_surj x) as [Z [z H]].
  subst x.
  rewrite Colim_map_TypObj, !TypCocomp.map_Obj.
  simpl.
  apply pnatural.
Qed.
Next Obligation.
  natural_eq Y.
  apply Presheave.hom_eq; simpl.
  intros Z z.
  apply TypCocomp.map_Obj.
Qed.
Next Obligation.
  apply Presheave.hom_eq; simpl.
  intros Y x.
  destruct (TypCocomp.Obj_surj x) as [Z [z H]].
  subst x.
  apply TypCocomp.map_Obj.
Qed.

Canonical PresheaveCocomp C := Cocomplete.Pack (Presheave.cat C) (PresheaveCocomp_mixin C).

Program Definition PresheaveTop_mixin C := TopCategory.Mixin (Presheave.cat C)
  {|
    pobj _ := 1;
    pmap X Y f x := x;
  |}
  (fun P => {|
    ptrans _ _ := tt;
  |})
  _.
Next Obligation.
  apply Presheave.hom_eq; simpl.
  intros X x.
  now destruct (f X x).
Qed.

Canonical PresheaveTop C := TopCategory.Pack (Presheave.cat C) (PresheaveTop_mixin C).

Program Definition PresheaveProd_mixin C := ProdCategory.Mixin (Presheave.cat C)
  (fun P Q => {|
    pobj X := (P X * Q X)%type;
    pmap X Y f p:= (pmap P f (fst p), pmap Q f (snd p));
  |})
  (fun P Q R η ϵ => {|
    ptrans X x := (η X x, ϵ X x);
  |})
  (fun P Q => {|
    ptrans X p := fst p;
  |})
  (fun P Q => {|
    ptrans X p := snd p;
  |})
  _.
Next Obligation.
  f_equal; apply pmap_id.
Qed.
Next Obligation.
  f_equal; apply pmap_comp.
Qed.
Next Obligation.
  f_equal; apply pnatural.
Qed.
Next Obligation.
  split.
  + intros H.
    subst h.
    split.
    all: now apply Presheave.hom_eq.
  + intros [].
    subst f g.
    apply Presheave.hom_eq; simpl.
    intros X x.
    now destruct (h X x).
Qed.

Canonical PresheaveProd C := ProdCategory.Pack (Presheave.cat C) (PresheaveProd_mixin C).

Definition PresheaveCart_class C := CartCategory.Class (Presheave.cat C) (PresheaveTop_mixin C) (PresheaveProd_mixin C).
Canonical PresheaveCart C := CartCategory.Pack (Presheave.cat C) (PresheaveCart_class C).

Program Definition PresheaveExp_mixin C := ExpCategory.Mixin (PresheaveProd C)
  (fun T S => {|
    pobj X := yoneda X × S ~> T;
    pmap X Y f η := {|
      ptrans Z p := η Z (f ∘ fst p, snd p);
    |};
  |})
  (fun T S => {|
    ptrans X p := fst p X (id X, snd p);
  |})
  (fun T S P η => {|
    ptrans X x := {|
      ptrans Y p := (η Y (pmap P (fst p) x, snd p));
    |};
  |})
  _.
Next Obligation.
  simpl.
  rewrite <- pnatural; simpl.
  do 2 f_equal.
  apply comp_assoc.
Qed.
Next Obligation.
  rename x into η.
  apply Presheave.hom_eq; simpl.
  intros Y [f x]; simpl.
  do 2 f_equal.
  apply comp_id_l.
Qed.
Next Obligation.
  rename x into η.
  apply Presheave.hom_eq; simpl.
  intros V [h x]; simpl.
  do 2 f_equal.
  symmetry.
  apply comp_assoc.
Qed.
Next Obligation.
  rewrite <- pnatural; simpl.
  do 2 f_equal.
  rewrite comp_id_l.
  apply comp_id_r.
Qed.
Next Obligation.
  rewrite <- pnatural; simpl.
  do 2 f_equal.
  apply pmap_comp.
Qed.
Next Obligation.
  apply Presheave.hom_eq; simpl.
  intros Z [g z]; simpl.
  do 2 f_equal.
  symmetry.
  apply pmap_comp.
Qed.
Next Obligation.
  rename t into T, s into S, x into P, f into η, g into ϵ.
  split; intros H.
  + subst η.
    apply Presheave.hom_eq; simpl.
    intros X x.
    apply Presheave.hom_eq; simpl.
    intros Y [f y]; simpl.
    rewrite pnatural; simpl.
    do 2 f_equal.
    apply comp_id_r.
  + subst ϵ.
    apply Presheave.hom_eq; simpl.
    intros X [x y]; simpl.
    do 2 f_equal.
    apply pmap_id.
Qed.

Definition PresheaveExp_class C := ExpCategory.Class (Presheave.cat C) (PresheaveProd_mixin C) (PresheaveExp_mixin C).
Canonical PresheaveExp C := ExpCategory.Pack (Presheave.cat C) (PresheaveExp_class C).

Definition PresheaveCCC_class C := CCC.Class (Presheave.cat C) (PresheaveCart_class C) (PresheaveExp_mixin C).
Canonical PresheaveCCC C := CCC.Pack (Presheave.cat C) (PresheaveCCC_class C).

Module Elm.
Structure obj {C: Category} (P: Presheave C) := {
  eobj: C;
  elm: P eobj;
}.

Arguments eobj {C P} _.
Arguments elm {C P} _.

Structure hom {C: Category} {P: Presheave C} (X Y: obj P) := {
  emap: eobj X ~> eobj Y;
  emap_comm: pmap P emap (elm Y) = elm X;
}.

Arguments emap {C P X Y} _.
Arguments emap_comm {C P X Y} _.

Lemma hom_eq {C: Category} {P: Presheave C} {X Y: obj P} (f g: hom X Y): f = g <-> emap f = emap g.
Proof.
  split.
  now intros [].
  destruct f as [f Hf], g as [g Hg]; simpl.
  intros H.
  subst g.
  f_equal; apply proof_irrelevance.
Qed.

Section cat.
Context {C: Category} (P: Presheave C).

Let id (X: obj P) := {|
  emap := id (eobj X);
  emap_comm := pmap_id P (elm X);
|}.

Let comp {X Y Z: obj P} (f: hom Y Z) (g: hom X Y) := {|
  emap := emap f ∘ emap g;
  emap_comm := eq_trans (pmap_comp P (emap f) (emap g) (elm Z)) (eq_trans (f_equal (pmap P (emap g)) (emap_comm f)) (emap_comm g));
|}.

Lemma comp_assoc {X Y Z V: obj P} (f: hom Z V) (g: hom Y Z) (h: hom X Y): comp f (comp g h) = comp (comp f g) h.
Proof. apply hom_eq, comp_assoc. Qed.

Lemma comp_id_l {X Y: obj P} (f: hom X Y): comp (id Y) f = f.
Proof. apply hom_eq, comp_id_l. Qed.

Lemma comp_id_r {X Y: obj P} (f: hom X Y): comp f (id X) = f.
Proof. apply hom_eq, comp_id_r. Qed.

Definition cat_mixin := Category.Mixin (obj P) hom id (@comp) (@comp_assoc) (@comp_id_l) (@comp_id_r).
Definition cat := Category.Pack (obj P) cat_mixin.

End cat.

Canonical cat.

Definition img {C} {P Q: Presheave C} (η: P ~> Q) (X: obj P): obj Q := {|
  eobj := eobj X;
  elm := η (eobj X) (elm X);
|}.

Program Definition img_inc {C} {P Q: Presheave C} (η: P ~> Q) (X Y: obj P) (f: X ~> Y): img η X ~> img η Y := {|
  emap := emap f;
|}.
Next Obligation.
  rewrite <- (pnatural η).
  f_equal.
  apply emap_comm.
Qed.

Program Canonical Img {C} {P Q: Presheave C} (η: P ~> Q): Functor (cat P) (cat Q) := {|
  fobj := img η;
  fmap := img_inc η;
|}.
Next Obligation.
  now apply hom_eq.
Qed.
Next Obligation.
  now apply hom_eq.
Qed.

Program Canonical FCat {C}: Functor (Presheave.cat C) Cat := {|
  fobj := cat;
  fmap := @Img C;
|}.
Next Obligation.
  fun_eq X Y f.
  now destruct x.
  apply hom_eq; simpl.
  destruct X as [X x], Y as [Y y], f as [f Hf]; simpl in *.
  rewrite !eq_iso_refl; simpl.
  rewrite (Categories.comp_id_r f).
  exact (Categories.comp_id_l f).
Qed.
Next Obligation.
  fun_eq X Y h.
  rewrite !eq_iso_refl; simpl.
  apply hom_eq; simpl.
  rewrite Categories.comp_id_r.
  apply Categories.comp_id_l.
Qed.

Program Canonical proj {C: Category} (P: Presheave C): Functor (cat P) C := {|
  fobj := @eobj C P;
  fmap := @emap C P;
|}.

Lemma proj_map {C} {P Q: Presheave C} (η: P ~> Q): proj P = proj Q ∘ Img η.
Proof. now fun_eq X Y f. Qed.

End Elm.

Canonical Elm.cat.
Notation "∫ P" := (Elm.cat P) (at level 35, right associativity).
Canonical Elm.Img.
Canonical Elm.FCat.
Canonical Elm.proj.

Program Definition R {C: Category} {𝓔: Cocomplete} (A: Functor C 𝓔): Functor 𝓔 (Presheave.cat C) := {|
  fobj E := {|
    pobj X := A X ~> E;
    pmap X Y f g := g ∘ fmap A f;
  |};
  fmap E F f := {|
    ptrans X := comp f;
  |}
|}.
Next Obligation.
  rewrite fmap_id.
  apply comp_id_r.
Qed.
Next Obligation.
  rewrite <- comp_assoc.
  f_equal.
  apply fmap_comp.
Qed.
Next Obligation.
  apply comp_assoc.
Qed.
Next Obligation.
  apply Presheave.hom_eq; simpl.
  intros X x.
  apply comp_id_l.
Qed.
Next Obligation.
  apply Presheave.hom_eq; simpl.
  intros X x.
  symmetry.
  apply comp_assoc.
Qed.

Program Definition L {C: Category} {𝓔: Cocomplete} (A: Functor C 𝓔): Functor (Presheave.cat C) 𝓔 := {|
  fobj P := colim (A ∘ Elm.proj P);
  fmap P Q η := map_Colimit (A ∘ Elm.proj Q) (Elm.Img η) ∘ Colim_map (α A (Elm.proj Q) (Elm.Img η) ∘ (A <| eq_iso (Elm.proj_map η)));
|}.
Next Obligation.
  apply is_eq_refl.
  apply is_eq_comp.
  apply fmap_is_eq.
  apply is_eq_comp.
  apply is_eq_whisk_l, eq_iso_is_eq.
  apply nat_is_eq.
  intros x.
  apply is_eq_id.
  apply map_Colimit_is_eq.
  apply fmap_is_eq, is_eq_id.
Qed.
Next Obligation.
  apply from_colim_eq.
  intros x.
  rewrite <- !comp_assoc.
  rewrite <- (comp_assoc (map_Colimit _ _)).
  rewrite !Colim_map_Colim; simpl.
  rewrite comp_assoc.
  rewrite (comp_assoc (map_Colimit _ (Elm.Img g))).
  etransitivity.
  etransitivity.
  3: symmetry.
  1: apply (f_equal (fun f => f ∘ _)).
  3: apply (f_equal (fun f => _ ∘ (_ ∘ (f ∘ _)))).
  1, 3: exact (map_Colimit_Colim (A ∘ Elm.proj _) (Elm.Img _) x).
  simpl.
  rewrite (comp_assoc (Colim_map _)).
  etransitivity.
  2: symmetry.
  2: apply (f_equal (fun f => _ ∘ (f ∘ _))).
  2: exact (@Colim_map_Colim _ _ (A ∘ Elm.proj b) _ _ (Elm.Img g x)).
  simpl.
  rewrite !comp_assoc.
  etransitivity.
  2: symmetry.
  2: apply (f_equal (fun f => f ∘ _ ∘ _ ∘ _ ∘ _)).
  2: exact (map_Colimit_Colim (A ∘ Elm.proj c) (Elm.Img f) (Elm.Img g x)).
  simpl.
  rewrite !comp_id_r.
  rewrite <- comp_assoc, <- fmap_comp.
  do 2 f_equal.
  apply is_eq_unique, is_eq_comp.
  apply transform_is_eq, eq_iso_is_eq.
  apply (transform_is_eq (eq_iso (Elm.proj_map g))), eq_iso_is_eq.
  apply (transform_is_eq (eq_iso (Elm.proj_map f)) (Elm.Img g x)), eq_iso_is_eq.
Qed.
