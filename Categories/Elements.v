Require Export Categories.Comma.
Require Export Categories.Pointed.
Require Export Instances.Typ.
Require Export Instances.Cat.
Require Export Yoneda.

Module El.
Section category.
Context {C: Category} {P: Functor C Typ}.

Structure obj := Obj {
  carrier: C;
  element: P carrier;
}.

Local Coercion carrier: obj >-> Category.obj.

Structure hom (X Y: obj) := Hom {
  arr: X ~> Y;
  comm: fmap P arr (element X) = element Y;
}.

Global Arguments Hom {X Y} arr comm.
Global Arguments arr {X Y} _.
Global Arguments comm {X Y} _.
Local Coercion arr: hom >-> Categories.hom.

Lemma obj_eq (X Y: obj): X = Y <-> carrier X = Y /\ forall e: carrier X = Y, match e in (_ = y) return P y with eq_refl => element X end = element Y.
Proof.
  split.
  + intros H.
    subst Y.
    split.
    reflexivity.
    intros e.
    rewrite (proof_irrelevance _ e eq_refl).
    reflexivity.
  + destruct X as [X x], Y as [Y y].
    simpl.
    intros [Hc He].
    subst Y.
    specialize (He eq_refl).
    now f_equal.
Qed.

Lemma hom_eq {X Y: obj} (f g: hom X Y): f = g <-> arr f = g.
Proof.
  split.
  intros H.
  now subst g.
  destruct f as [f Hf], g as [g Hg].
  simpl.
  intros H.
  subst g.
  f_equal.
  apply proof_irrelevance.
Qed.

Program Let id (X: obj): hom X X := {|
  arr := id X;
|}.
Next Obligation.
  now rewrite (@fmap_id _ _ P).
Qed.

Program Let comp {X Y Z: obj} (f: hom Y Z) (g: hom X Y): hom X Z := {|
  arr := f ∘ g;
|}.
Next Obligation.
  etransitivity.
  apply (f_equal (fun f => f _)).
  apply (@fmap_comp _ _ P).
  unfold comp; simpl.
  rewrite comm.
  apply comm.
Qed.

Lemma comp_assoc {X Y Z V: obj} (f: hom Z V) (g: hom Y Z) (h: hom X Y): comp f (comp g h) = comp (comp f g) h.
Proof.
  apply hom_eq; simpl.
  apply comp_assoc.
Qed.

Lemma comp_id_l {X Y: obj} (f: hom X Y): comp (id Y) f = f.
Proof.
  apply hom_eq; simpl.
  apply comp_id_l.
Qed.

Lemma comp_id_r {X Y: obj} (f: hom X Y): comp f (id X) = f.
Proof.
  apply hom_eq; simpl.
  apply comp_id_r.
Qed.

Definition cat_mixin: Category.mixin_of obj :=
  Category.Mixin obj hom id (@comp) (@comp_assoc) (@comp_id_l) (@comp_id_r).

Canonical cat := Category.Pack obj cat_mixin.

End category.
Arguments obj {C} P.
Arguments cat {C} P.

Definition proj {C: Category} (P: Functor C Typ): cat P ~> C := {|
  fobj := carrier;
  fmap := @arr C P;
  fmap_id _ := eq_refl;
  fmap_comp _ _ _ _ _ := eq_refl;
|}.

Program Definition forget {C: Category} (P: Functor C Typ): cat P ~> Pointed TypTop := {|
  fobj X := {|
    Pointed.carrier := P (carrier X);
    Pointed.element _ := element X;
  |};
  fmap X Y f := {|
    Pointed.arr := fmap P (arr f);
  |};
|}.
Next Obligation.
  extensionality x.
  apply comm.
Qed.
Next Obligation.
  apply Pointed.hom_eq; simpl.
  apply fmap_id.
Qed.
Next Obligation.
  apply Pointed.hom_eq; simpl.
  apply fmap_comp.
Qed.

End El.

Canonical El.cat.
Notation El := El.cat.

Program Definition el {C: Category}: Functor (Fun C Typ) Cat := {|
  fobj := El;
  fmap F G η := {|
    fobj X := {|
      El.carrier := El.carrier X;
      El.element := η (El.carrier X) (El.element X);
    |};
    fmap X Y f := {|
      El.arr := El.arr f;
    |};
  |};
|}.
Next Obligation.
  rewrite <- (El.comm f).
  change ((fmap G (El.arr f) ∘ η (El.carrier X)) (El.element X) = (η (El.carrier Y) ∘ fmap F (El.arr f)) (El.element X)).
  apply (f_equal (fun f => f _)).
  symmetry.
  apply (naturality η).
Qed.
Next Obligation.
  now apply El.hom_eq.
Qed.
Next Obligation.
  now apply El.hom_eq.
Qed.
Next Obligation.
  rename a into F.
  fun_eq X Y f.
  now destruct x as [X x].
  destruct X as [X x], Y as [Y y], f as [f Hf].
  rewrite !eq_iso_refl; clear H H0.
  simpl in *.
  subst y.
  apply El.hom_eq; simpl.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.
Next Obligation.
  rename a into F, b into G, c into H, f into η, g into ϵ.
  fun_eq X Y f.
  rewrite !eq_iso_refl; clear H0 H1.
  apply El.hom_eq; simpl.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Module CoEl.
Section category.
Context {C: Category} {P: Functor (co C) Typ}.

Structure obj := Obj {
  carrier: C;
  element: P carrier;
}.

Local Coercion carrier: obj >-> Category.obj.

Structure hom (X Y: obj) := Hom {
  arr: X ~> Y;
  comm: fmap P arr (element Y) = element X;
}.

Global Arguments Hom {X Y} arr comm.
Global Arguments arr {X Y} _.
Global Arguments comm {X Y} _.
Local Coercion arr: hom >-> Categories.hom.

Lemma obj_eq (X Y: obj): X = Y <-> carrier X = Y /\ forall e: carrier X = Y, match e in (_ = y) return P y with eq_refl => element X end = element Y.
Proof.
  split.
  + intros H.
    subst Y.
    split.
    reflexivity.
    intros e.
    rewrite (proof_irrelevance _ e eq_refl).
    reflexivity.
  + destruct X as [X x], Y as [Y y].
    simpl.
    intros [Hc He].
    subst Y.
    specialize (He eq_refl).
    now f_equal.
Qed.

Lemma hom_eq {X Y: obj} (f g: hom X Y): f = g <-> arr f = g.
Proof.
  split.
  intros H.
  now subst g.
  destruct f as [f Hf], g as [g Hg].
  simpl.
  intros H.
  subst g.
  f_equal.
  apply proof_irrelevance.
Qed.

Program Let id (X: obj): hom X X := {|
  arr := id X;
|}.
Next Obligation.
  now rewrite (@fmap_id _ _ P).
Qed.

Program Let comp {X Y Z: obj} (f: hom Y Z) (g: hom X Y): hom X Z := {|
  arr := f ∘ g;
|}.
Next Obligation.
  etransitivity.
  apply (f_equal (fun f => f _)).
  apply (@fmap_comp _ _ P).
  unfold comp; simpl.
  rewrite comm.
  apply comm.
Qed.

Lemma comp_assoc {X Y Z V: obj} (f: hom Z V) (g: hom Y Z) (h: hom X Y): comp f (comp g h) = comp (comp f g) h.
Proof.
  apply hom_eq; simpl.
  apply comp_assoc.
Qed.

Lemma comp_id_l {X Y: obj} (f: hom X Y): comp (id Y) f = f.
Proof.
  apply hom_eq; simpl.
  apply comp_id_l.
Qed.

Lemma comp_id_r {X Y: obj} (f: hom X Y): comp f (id X) = f.
Proof.
  apply hom_eq; simpl.
  apply comp_id_r.
Qed.

Definition cat_mixin: Category.mixin_of obj :=
  Category.Mixin obj hom id (@comp) (@comp_assoc) (@comp_id_l) (@comp_id_r).

Canonical cat := Category.Pack obj cat_mixin.

End category.
Arguments obj {C} P.
Arguments cat {C} P.

Definition proj {C: Category} (P: Functor (co C) Typ): cat P ~> C := {|
  fobj := carrier;
  fmap := @arr C P;
  fmap_id _ := eq_refl;
  fmap_comp _ _ _ _ _ := eq_refl;
|}.

End CoEl.

Canonical CoEl.cat.
Notation CoEl := CoEl.cat.

Program Definition coel {C: Category}: Functor (Fun (co C) Typ) Cat := {|
  fobj := CoEl;
  fmap F G η := {|
    fobj X := {|
      CoEl.carrier := CoEl.carrier X;
      CoEl.element := η (CoEl.carrier X) (CoEl.element X);
    |};
    fmap X Y f := {|
      CoEl.arr := CoEl.arr f;
    |};
  |};
|}.
Next Obligation.
  rewrite <- (CoEl.comm f).
  change ((fmap G (CoEl.arr f) ∘ η (CoEl.carrier Y)) (CoEl.element Y) = (η (CoEl.carrier X) ∘ fmap F (CoEl.arr f)) (CoEl.element Y)).
  apply (f_equal (fun f => f _)).
  symmetry.
  apply (naturality η).
Qed.
Next Obligation.
  now apply CoEl.hom_eq.
Qed.
Next Obligation.
  now apply CoEl.hom_eq.
Qed.
Next Obligation.
  rename a into F.
  fun_eq X Y f.
  now destruct x as [X x].
  destruct X as [X x], Y as [Y y], f as [f Hf].
  rewrite !eq_iso_refl; clear H H0.
  simpl in *.
  subst x.
  apply CoEl.hom_eq; simpl.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.
Next Obligation.
  rename a into F, b into G, c into H, f into η, g into ϵ.
  fun_eq X Y f.
  rewrite !eq_iso_refl; clear H0 H1.
  apply CoEl.hom_eq; simpl.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Section El_co.
Context {C: Category} (P: Functor (co C) Typ).

Program Definition El_co_to: co (El P) ~> CoEl P := {|
  fobj X := {|
    CoEl.carrier := El.carrier X;
    CoEl.element := El.element X;
  |};
  fmap X Y f := {|
    CoEl.arr := El.arr f;
    CoEl.comm := El.comm f;
  |};
|}.
Next Obligation.
  now apply CoEl.hom_eq.
Qed.
Next Obligation.
  now apply CoEl.hom_eq.
Qed.

Program Definition El_co_from: CoEl P ~> co (El P) := {|
  fobj X := {|
    El.carrier := CoEl.carrier X;
    El.element := CoEl.element X;
  |};
  fmap X Y f := {|
    El.arr := CoEl.arr f;
    El.comm := CoEl.comm f;
  |};
|}.
Next Obligation.
  now apply El.hom_eq.
Qed.
Next Obligation.
  now apply El.hom_eq.
Qed.

Lemma El_co_inv_l: El_co_from ∘ El_co_to = id (co (El P)).
Proof.
  fun_eq X Y f.
  now destruct x.
  destruct X as [X x], Y as [Y y], f as [f Hf].
  simpl in *.
  rewrite !eq_iso_refl; clear H H0.
  simpl.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Lemma El_co_inv_r: El_co_to ∘ El_co_from = id (CoEl P).
Proof.
  fun_eq X Y f.
  now destruct x.
  destruct X as [X x], Y as [Y y], f as [f Hf].
  simpl in *.
  rewrite !eq_iso_refl; clear H H0.
  simpl.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Definition El_co: co (El P) <~> CoEl P :=
  Isomorphism.Pack El_co_to (Isomorphism.Mixin _ _ _ El_co_to El_co_from El_co_inv_l El_co_inv_r).

End El_co.

Section el_co.
Context {C: Category}.

Program Definition el_co_to: Co' ∘ el ~> @coel C := {|
  transform P := to (El_co P);
  naturality P Q η := _;
|}.
Next Obligation.
  fun_eq X Y f.
  now apply CoEl.hom_eq.
Qed.

Program Definition el_co_from: @coel C ~> Co' ∘ el := {|
  transform P := to (El_co P)⁻¹;
  naturality P Q η := _;
|}.
Next Obligation.
  fun_eq X Y f.
  rewrite !eq_iso_refl; clear H H0.
  simpl.
  rewrite comp_id_l, comp_id_r.
  now apply El.hom_eq.
Qed.

Lemma el_co_inv_l: el_co_from ∘ el_co_to = id (Co' ∘ el).
Proof.
  natural_eq P.
  apply (inv_l (El_co P)).
Qed.

Lemma el_co_inv_r: el_co_to ∘ el_co_from = id coel.
Proof.
  natural_eq P.
  apply (inv_r (El_co P)).
Qed.

Definition el_co: Co' ∘ el <~> @coel C :=
  Isomorphism.Pack el_co_to (Isomorphism.Mixin _ _ _ el_co_to el_co_from el_co_inv_l el_co_inv_r).

End el_co.

Section CoEl_comma.
Context {C: Category} (P: Functor (co C) Typ).

Program Definition CoEl_comma_to: CoEl P ~> よ C ↓ @Δ _ 1 P := {|
  fobj X := {|
    Comma.source := CoEl.carrier X;
    Comma.target := 1;
    Comma.morph := {|
      transform x f := fmap P f (CoEl.element X);
    |};
  |};
  fmap X Y f := {|
    Comma.smap := CoEl.arr f;
    Comma.tmap := id 1;
  |};
|}.
Next Obligation.
  extensionality g.
  change (fmap P (g ∘ f) (CoEl.element X) = (fmap P f ∘ fmap P g) (CoEl.element X)).
  apply (f_equal (fun f => f _)).
  apply (@fmap_comp _ _ P).
Qed.
Next Obligation.
  natural_eq x.
  extensionality g.
  unfold id, comp at 1 2; simpl.
  etransitivity.
  2: symmetry.
  2: apply (f_equal (fun f => f _)).
  2: apply (@fmap_comp _ _ P).
  unfold comp; simpl.
  f_equal.
  symmetry.
  apply CoEl.comm.
Qed.
Next Obligation.
  now apply Comma.hom_eq.
Qed.
Next Obligation.
  now apply Comma.hom_eq.
Qed.

Program Definition CoEl_comma_from: よ C ↓ @Δ _ 1 P ~> CoEl P := {|
  fobj X := {|
    CoEl.carrier := Comma.source X;
    CoEl.element := Comma.morph X (Comma.source X) (id (Comma.source X));
  |};
  fmap X Y f := {|
    CoEl.arr := Comma.smap f;
  |};
|}.
Next Obligation.
  specialize (proj1 (natural_eq _ _) (Comma.comm _ _ _ _ f) (Comma.source X)) as H.
  simpl in H.
  apply (f_equal (fun f => f (id (Comma.source X)))) in H.
  change (Comma.morph X (Comma.source X) (id (Comma.source X)) = Comma.morph Y (Comma.source X) (Comma.smap f ∘ id (Comma.source X))) in H.
  rewrite (comp_id_r (Comma.smap f)) in H.
  etransitivity.
  2: symmetry.
  2: exact H.
  clear H.
  specialize (naturality (Comma.morph Y) (Comma.smap f)) as H.
  apply (f_equal (fun f => f (id (Comma.source Y)))) in H.
  unfold comp in H; simpl in H.
  rewrite comp_id_l in H.
  now symmetry.
Qed.
Next Obligation.
  now apply CoEl.hom_eq.
Qed.
Next Obligation.
  now apply CoEl.hom_eq.
Qed.

Lemma CoEl_comma_inv_l: CoEl_comma_from ∘ CoEl_comma_to = id (CoEl P).
Proof.
  fun_eq X Y f.
  destruct x as [X x]; simpl.
  f_equal.
  now rewrite (@fmap_id _ _ P).
  apply CoEl.hom_eq; simpl.
  etransitivity.
  etransitivity.
  apply (f_equal (fun f => f ∘ _)).
  3: symmetry.
  3: apply (f_equal (fun f => _ ∘ f)).
  1, 3: apply is_eq_refl.
  1: destruct H0.
  2: destruct H.
  1, 2: apply is_eq_id.
  clear H H0.
  rewrite comp_id_r.
  apply comp_id_l.
Qed.

Lemma CoEl_comma_inv_r: CoEl_comma_to ∘ CoEl_comma_from = id (よ C ↓ Δ P).
Proof.
  fun_eq X Y f.
  destruct x as [X [] η]; simpl.
  f_equal.
  natural_eq x.
  extensionality f.
  specialize (naturality η f) as H.
  apply (f_equal (fun f => f (id X))) in H.
  simpl in H.
  unfold comp at 1 4 in H; simpl in H.
  rewrite comp_id_l in H.
  now symmetry.
  apply Comma.hom_eq; simpl; split.
  etransitivity.
  etransitivity.
  apply (f_equal (fun f => f ∘ _)).
  3: symmetry.
  3: apply (f_equal (fun f => _ ∘ f)).
  1, 3: apply is_eq_refl.
  1: destruct H0.
  2: destruct H.
  1, 2: apply is_eq_id.
  clear H H0.
  rewrite comp_id_r.
  apply comp_id_l.
  apply unit_eq.
Qed.

Definition CoEl_comma: CoEl P <~> よ C ↓ @Δ _ 1 P :=
  Isomorphism.Pack CoEl_comma_to (Isomorphism.Mixin _ _ _ CoEl_comma_to CoEl_comma_from CoEl_comma_inv_l CoEl_comma_inv_r).

End CoEl_comma.

Lemma el_adj
