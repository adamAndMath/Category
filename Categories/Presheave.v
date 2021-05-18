Require Export Categories.Typ.

Structure Presheave (C: Category) := {
  pobj: C -> Type;
  pmap {X Y: C}: Y ~> X -> pobj X -> pobj Y;
  pmap_id {X: C} (x: pobj X): pmap (id X) x = x;
  pmap_comp {X Y Z: C} (f: Y ~> Z) (g: X ~> Y) (x: pobj Z): pmap (f ∘ g) x = pmap g (pmap f x);
}.

Arguments pobj {C} _ _.
Arguments pmap {C} _ {X Y} _ _.
Arguments pmap_id {C} _ {X} _.
Arguments pmap_comp {C} _ {X Y Z} _ _ _.

Coercion pobj: Presheave >-> Funclass.

Program Definition psfun {C: Category} (P: Presheave C): Functor (co C) Typ := Build_Functor (co C) Typ
  P (@pmap C P) _ _.
Next Obligation.
  extensionality x.
  exact (pmap_id P x).
Qed.
Next Obligation.
  extensionality x.
  exact (pmap_comp P g f x).
Qed.

Coercion psfun: Presheave >-> Functor.
Canonical psfun.

Module Presheave.

Structure hom {C: Category} (P Q: Presheave C) := {
  ptrans (X: C): P X -> Q X;
  pnatural {X Y: C} (f: X ~> Y) (x: P Y): ptrans X (pmap P f x) = pmap Q f (ptrans Y x);
}.

Arguments ptrans {C P Q} _ {X} _.
Arguments pnatural {C P Q} _ {X Y} _ _.
Coercion ptrans: hom >-> Funclass.

Lemma hom_eq {C: Category} {P Q: Presheave C} (η ϵ: hom P Q): η = ϵ <-> forall X (x: P X), η X x = ϵ X x.
Proof.
  split.
  now intros [].
  destruct η as [f Hf], ϵ as [g Hg]; simpl.
  intros H.
  enough (f = g); [subst g|].
  f_equal; apply proof_irrelevance.
  extensionality X.
  extensionality x.
  apply H.
Qed.

Section cat.
Context {C: Category}.

Let id (P: Presheave C): hom P P := {|
  ptrans X x := x;
  pnatural X Y f x := eq_refl;
|}.

Program Let comp {P Q R: Presheave C} (η: hom Q R) (ϵ: hom P Q): hom P R := {|
  ptrans X x := η X (ϵ X x);
|}.
Next Obligation.
  rewrite pnatural.
  apply pnatural.
Qed.

Lemma comp_assoc {P Q R S: Presheave C} (η: hom R S) (ϵ: hom Q R) (γ: hom P Q): comp η (comp ϵ γ) = comp (comp η ϵ) γ.
Proof. now apply hom_eq. Qed.

Lemma comp_id_l {P Q: Presheave C} (η: hom P Q): comp (id Q) η = η.
Proof. now apply hom_eq. Qed.

Lemma comp_id_r {P Q: Presheave C} (η: hom P Q): comp η (id P) = η.
Proof. now apply hom_eq. Qed.

Definition cat_mixin := Category.Mixin (Presheave C) hom id (@comp) (@comp_assoc) (@comp_id_l) (@comp_id_r).

End cat.

Canonical cat (C: Category) := Category.Pack (Presheave C) cat_mixin.

Lemma ptrans_is_eq {C} {P Q: Presheave C} (η: P ~> Q) (X: C): is_eq η -> @is_eq Typ _ _ (η X).
Proof.
  intros [e H].
  subst η Q; simpl.
  exact is_eq_id.
Qed.

Program Definition preimg {C D: Category} (F: Functor D C) (P: Presheave C): Presheave D := {|
  pobj X := P (F X);
  pmap X Y f x := pmap P (fmap F f) x;
|}.
Next Obligation.
  rewrite fmap_id.
  apply pmap_id.
Qed.
Next Obligation.
  rewrite fmap_comp.
  apply pmap_comp.
Qed.

Program Definition preimg_inc {C D: Category} (F: Functor D C) (P Q: Presheave C) (η: P ~> Q): preimg F P ~> preimg F Q := {|
  ptrans X x := η (F X) x;
  pnatural X Y f := pnatural η (fmap F f);
|}.

Program Canonical Preimg {C D: Category} (F: Functor D C): Functor (cat C) (cat D) := {|
  fobj := preimg F;
  fmap := preimg_inc F;
|}.
Next Obligation.
  now apply hom_eq.
Qed.

Program Canonical FCat: Functor (co Cat) Cat := {|
  fobj := cat;
  fmap := @Preimg;
|}.
Next Obligation.
  fun_eq P Q η.
  unfold preimg.
  destruct x; simpl.
  f_equal; apply proof_irrelevance.
  apply hom_eq; simpl.
  intros X x.
  rewrite (@is_eq_refl Typ (Q X) (to (eq_iso H0) X)).
  rewrite (@is_eq_refl Typ (P X) (to (eq_iso H) X)).
  reflexivity.
  1: apply (ptrans_is_eq (eq_iso H)).
  2: apply (ptrans_is_eq (eq_iso H0)).
  all: apply eq_iso_is_eq.
Qed.
Next Obligation.
  fun_eq P Q η.
  unfold preimg; simpl.
  f_equal; apply proof_irrelevance.
  apply hom_eq; simpl.
  intros X x.
  rewrite (@is_eq_refl Typ _ (to (eq_iso H0) X)).
  rewrite (@is_eq_refl Typ _ (to (eq_iso H) X)).
  reflexivity.
  1: apply (ptrans_is_eq (eq_iso H)).
  2: apply (ptrans_is_eq (eq_iso H0)).
  all: apply eq_iso_is_eq.
Qed.

End Presheave.

Notation ptrans := Presheave.ptrans.
Notation pnatural := Presheave.pnatural.
Coercion ptrans: Presheave.hom >-> Funclass.
Canonical Presheave.cat.
Canonical Presheave.Preimg.
Canonical Presheave.FCat.

Program Definition psnat {C: Category} {P Q: Presheave C} (η: Presheave.hom P Q): Natural P Q := Build_Natural (co C) Typ P Q
  η _.
Next Obligation.
  extensionality e.
  apply pnatural.
Qed.

Coercion psnat: Presheave.hom >-> Natural.
Canonical psnat.

Section Psfun.
Context {C: Category}.

Program Definition Psfun_to: Presheave.cat C ~> Fun (co C) Typ := {|
  fobj := psfun;
  fmap := @psnat C;
|}.
Next Obligation.
  now natural_eq x.
Qed.
Next Obligation.
  now natural_eq x.
Qed.

Program Definition Psfun_from: Functor (Fun (co C) Typ) (Presheave.cat C) := {|
  fobj P := {|
    pobj := P;
    pmap := @fmap _ _ P;
  |};
  fmap P Q η := {|
    ptrans := η;
  |}
|}.
Next Obligation.
  now rewrite (@fmap_id _ _ P).
Qed.
Next Obligation.
  change (f ∘ g) with (@comp (co C) _ _ _ g f).
  now rewrite (@fmap_comp _ _ P _ _ _ g f).
Qed.
Next Obligation.
  change ((η X ∘ fmap P f) x = (fmap Q f ∘ η Y) x).
  apply (f_equal (fun f => f x)).
  apply (@naturality _ _ _ _ η).
Qed.
Next Obligation.
  now apply Presheave.hom_eq.
Qed.
Next Obligation.
  now apply Presheave.hom_eq.
Qed.

Program Definition Psfun_mixin := Isomorphism.Mixin Cat (Presheave.cat C) (Fun (co C) Typ) Psfun_to Psfun_from _ _.
Next Obligation.
  fun_eq P Q η.
  destruct x; simpl.
  f_equal; apply proof_irrelevance.
  apply Presheave.hom_eq; simpl.
  intros X x.
  rewrite (@is_eq_refl Typ (Q X) (to (eq_iso H0) X)).
  rewrite (@is_eq_refl Typ (P X) (to (eq_iso H) X)).
  reflexivity.
  destruct H; simpl.
  exact (@is_eq_id Typ (P X)).
  destruct H0; simpl.
  exact (@is_eq_id Typ (Q X)).
Qed.
Next Obligation.
  fun_eq P Q η.
  destruct x; unfold psfun; simpl.
  f_equal; apply proof_irrelevance.
  natural_eq X.
  rewrite (is_eq_refl (to (eq_iso H0) X)).
  rewrite (is_eq_refl (to (eq_iso H) X)).
  rewrite comp_id_r.
  apply comp_id_l.
  1: destruct H; simpl.
  2: destruct H0; simpl.
  all: exact is_eq_id.
Qed.

Definition Psfun := Isomorphism.Pack Psfun_to Psfun_mixin.

End Psfun.

Canonical Psfun_to.
Canonical Psfun.

Definition psconst (C: Category) T := {|
  pobj (_: C) := T;
  pmap _ _ _ x := x;
  pmap_id _ x := eq_refl;
  pmap_comp _ _ _ _ _ x := eq_refl;
|}.

Definition yoneda {C: Category} (X: C): Presheave C := {|
  pobj Y := Y ~> X;
  pmap Y Z f g := g ∘ f;
  pmap_id Y f := comp_id_r f;
  pmap_comp Y Z V f g h := comp_assoc h f g;
|}.

Program Definition yoneda_map {C: Category} {X Y: C} (f: X ~> Y): yoneda X ~> yoneda Y := {|
  ptrans Z g := f ∘ g;
  pnatural Z V g h := comp_assoc f h g;
|}.

Program Canonical Yoneda {C: Category}: Functor C (Presheave.cat C) := {|
  fobj := yoneda;
  fmap := @yoneda_map C;
|}.
Next Obligation.
  apply Presheave.hom_eq; simpl.
  intros X f.
  apply comp_id_l.
Qed.
Next Obligation.
  apply Presheave.hom_eq; simpl.
  intros X h.
  symmetry.
  apply comp_assoc.
Qed.

Program Definition Yoneda_trans {C: Category} (P: Presheave C) (c: C) (x: P c): yoneda c ~> P := {|
  ptrans X f := pmap P f x;
|}.
Next Obligation.
  apply pmap_comp.
Qed.

Definition Yoneda_obj {C: Category} (P: Presheave C) (c: C) (η: yoneda c ~> P): P c := η c (id c).

Lemma Yoneda_obj_trans {C: Category} (P: Presheave C) (c: C) (x: P c): Yoneda_obj P c (Yoneda_trans P c x) = x.
Proof. apply pmap_id. Qed.

Lemma Yoneda_trans_obj {C: Category} (P: Presheave C) (c: C) (η: yoneda c ~> P): Yoneda_trans P c (Yoneda_obj P c η) = η.
Proof.
  apply Presheave.hom_eq; simpl.
  intros X f.
  unfold Yoneda_obj.
  rewrite <- pnatural; simpl.
  f_equal.
  apply comp_id_l.
Qed.

Lemma Yoneda_trans_surj {C: Category} (P: Presheave C) (c: C) (η: Yoneda c ~> P): exists! x, Yoneda_trans P c x = η.
Proof.
  exists (Yoneda_obj P c η); split.
  apply Yoneda_trans_obj.
  intros x Hη.
  subst η.
  apply Yoneda_obj_trans.
Qed.

Lemma Yoneda_lemma {C: Category} (c: C) (P: Presheave C): Hom (Presheave.cat C) (Yoneda c, P) ≃ P c.
Proof.
  constructor.
  exists (Yoneda_obj P c), (Yoneda_trans P c).
  simpl.
  1: extensionality η.
  2: extensionality x.
  all: unfold comp, id; simpl.
  apply Yoneda_trans_obj.
  apply Yoneda_obj_trans.
Qed.

Lemma Yoneda_full (C: Category): full (@Yoneda C).
Proof.
  intros x y η.
  exists (Yoneda_obj (yoneda y) x η).
  unfold Yoneda_obj; simpl.
  apply Presheave.hom_eq; simpl.
  intros z f.
  change (pmap (Yoneda y) f (η x (id x)) = η z f).
  rewrite <- pnatural; simpl.
  f_equal.
  apply comp_id_l.
Qed.

Lemma Yoneda_faithful (C: Category): faithful (@Yoneda C).
Proof.
  intros x y f g H.
  setoid_rewrite Presheave.hom_eq in H.
  simpl in H.
  specialize (H x (id x)).
  now rewrite !comp_id_r in H.
Qed.

Lemma Yoneda_fully_faithful (C: Category): fully_faithful (@Yoneda C).
Proof.
  apply full_and_faithful.
  split.
  apply Yoneda_full.
  apply Yoneda_faithful.
Qed.

(* fully_faithful_iso is currently to strict in its universes *)
Lemma Yoneda_principle {C: Category} (A B: C): Yoneda A ≃ Yoneda B <-> A ≃ B.
Proof.
  split.
  + intros [η].
    constructor.
    exists (to η A (id A)), (to η⁻¹ B (id B)).
    specialize (pnatural (to η⁻¹) (to η A (id A)) (id B)) as H.
    simpl in H |- *.
    rewrite <- H; clear H.
    rewrite comp_id_l.
    change ((η⁻¹ ∘ η) A (id A) = id (Yoneda A) A (id A)).
    f_equal.
    apply inv_l.
    specialize (pnatural (to η) (to η⁻¹ B (id B)) (id A)) as H.
    simpl in H |- *.
    rewrite <- H; clear H.
    rewrite comp_id_l.
    change ((η ∘ η⁻¹) B (id B) = id (Yoneda B) B (id B)).
    f_equal.
    apply inv_r.
  + intros [f].
    constructor.
    1: unshelve eexists.
    2: unshelve eexists.
    1: exists (fun Z g => f ∘ g).
    2: exists (fun Z g => f⁻¹ ∘ g).
    3, 4: apply Presheave.hom_eq.
    all: simpl.
    1, 2: intros X Y g h.
    1, 2: apply comp_assoc.
    all: intros X x.
    all: rewrite <- comp_id_l, comp_assoc.
    all: f_equal.
    apply inv_l.
    apply inv_r.
Qed.

Module TypColim.

Structure preObj {C: Category} (F: Presheave C) := PreObj {
  lobj: C;
  lelm: F lobj;
}.

Arguments PreObj {C F} lobj lelm.
Arguments lobj {C F} _.
Arguments lelm {C F} _.

Inductive equiv {C: Category} {F: Presheave C}: preObj F -> preObj F -> Prop :=
  | equiv_path {X Y Z: C} (f: Y ~> X) (g: Z ~> X) (x: F X): equiv (PreObj Y (pmap F f x)) (PreObj Z (pmap F g x))
  | equiv_trans X Y Z: equiv X Y -> equiv Y Z -> equiv X Z.

Instance equiv_inst (C: Category) (F: Presheave C): Equivalence (@equiv C F).
Proof.
  split.
  + intros [X x].
    change x with (id (F X) x).
    rewrite <- fmap_id.
    apply equiv_path.
  + intros X Y H.
    induction H.
    apply equiv_path.
    now apply (equiv_trans _ Y).
  + exact equiv_trans.
Qed.

Lemma equiv_step {C: Category} {X Y: C} (F: Presheave C) (f: Y ~> X) (x: F X): equiv (PreObj Y (pmap F f x)) (PreObj X x).
Proof.
  change x with (id (F X) x) at 2.
  rewrite <- fmap_id.
  apply equiv_path.
Qed.

Structure obj {C: Category} (F: Presheave C) := {
  class: preObj F -> Prop;
  class_inhabited: exists X, forall Y, class Y <-> equiv X Y;
}.

Arguments class {C F} _ _.
Arguments class_inhabited {C F} _.
Coercion class: obj >-> Funclass.

Instance class_proper (C: Category) (F: Presheave C): Proper (eq ==> @equiv C F ==> iff) class.
Proof.
  intros P Q e X Y H.
  subst Q.
  destruct (class_inhabited P) as [Z HZ].
  rewrite !HZ.
  now f_equiv.
Qed.

Program Definition Obj {C: Category} {F: Presheave C} (X: C) (x: F X) := {|
  class := equiv {| lobj := X; lelm := x |};
|}.
Next Obligation.
  now exists {| lobj := X; lelm := x |}.
Qed.

Lemma obj_eq {C: Category} {F: Presheave C} (X Y: obj F): X = Y <-> forall p, X p <-> Y p.
Proof.
  split.
  now intros [].
  destruct X as [X HX], Y as [Y HY]; simpl.
  intros H.
  enough (X = Y); [subst Y|].
  f_equal; apply proof_irrelevance.
  extensionality p.
  now apply propositional_extensionality.
Qed.

Lemma Obj_eq {C: Category} {F: Presheave C} (X: C) (x: F X) (Y: obj F): Obj X x = Y <-> Y (PreObj X x).
Proof.
  destruct (class_inhabited Y) as [y H].
  rewrite obj_eq; simpl; split.
  intros Hp.
  now apply Hp.
  intros Hx p.
  apply H in Hx.
  rewrite H.
  now f_equiv.
Qed.

Lemma Obj_surj {C: Category} {F: Presheave C} (X: obj F): exists Y (y: F Y), Obj Y y = X.
Proof.
  enough (exists Y (y: F Y), X {| lobj := Y; lelm := y |}) as [Y [y H]].
  exists Y, y.
  now apply Obj_eq.
  destruct X as [P HP]; simpl.
  destruct HP as [[X x] H].
  exists X, x.
  now apply H.
Qed.

Program Definition Into {C: Category} {F: Presheave C}: F ~> psconst C (obj F) := {|
  ptrans := Obj;
|}.
Next Obligation.
  apply Obj_eq; simpl.
  change x with (id (F Y) x) at 1.
  rewrite <- fmap_id.
  apply equiv_path.
Qed.

Lemma preObj_inhab {C: Category} {F: Presheave C} (X: obj F): inhabited (preObj F).
Proof. now destruct (class_inhabited X) as [x _]. Qed.

Definition map {C: Category} {F: Presheave C} {T: Type} (η: F ~> psconst C T) (X: obj F): T :=
  η (lobj (epsilon (preObj_inhab X) X)) (lelm (epsilon (preObj_inhab X) X)).

Lemma map_Obj {C: Category} {F: Presheave C} {T: Type} (η: F ~> psconst C T) (X: C) (x: F X): map η (Obj X x) = η X x.
Proof.
  unfold map.
  generalize (epsilon (preObj_inhab (Obj X x)) (Obj X x)), (epsilon_spec (preObj_inhab (Obj X x)) (Obj X x)).
  intros p H.
  assert (exists Y, Obj X x Y) by now exists (PreObj X x); simpl.
  specialize (H H0); clear H0.
  simpl in H.
  set (PreObj X x) in H.
  change X with (lobj p0).
  change x with (lelm p0).
  clearbody p0; clear X x.
  induction H; simpl.
  transitivity (η X x).
  2: symmetry.
  1, 2: apply (pnatural η).
  now transitivity (η (lobj Y) (lelm Y)).
Qed.

End TypColim.
