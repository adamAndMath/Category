Require Export Base.

Definition is_pullback {C: Category} {S A B T: C} (f: A ~> T) (g: B ~> T) (p1: S ~> A) (p2: S ~> B) :=
  f ∘ p1 = g ∘ p2 /\
  forall (Z: C) (q1: Z ~> A) (q2: Z ~> B), f ∘ q1 = g ∘ q2 -> exists! u: Z ~> S, p1 ∘ u = q1 /\ p2 ∘ u = q2.

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

Module PullCategory.

Structure mixin_of (C: Category) := Mixin {
  Pull {x y z: C}: x ~> z -> y ~> z -> C;
  pull1 {x y z: C} (f: x ~> z) (g: y ~> z): Pull f g ~> x;
  pull2 {x y z: C} (f: x ~> z) (g: y ~> z): Pull f g ~> y;
  pull_comm {x y z: C} (f: x ~> z) (g: y ~> z): f ∘ pull1 f g = g ∘ pull2 f g;
  pull_med {x y z v: C} (f: x ~> z) (g: y ~> z) (p1: v ~> x) (p2: v ~> y): f ∘ p1 = g ∘ p2 -> v ~> Pull f g;
  pull_med1 {x y z v: C} (f: x ~> z) (g: y ~> z) (p1: v ~> x) (p2: v ~> y) (H: f ∘ p1 = g ∘ p2): pull1 f g ∘ (pull_med f g p1 p2 H) = p1;
  pull_med2 {x y z v: C} (f: x ~> z) (g: y ~> z) (p1: v ~> x) (p2: v ~> y) (H: f ∘ p1 = g ∘ p2): pull2 f g ∘ (pull_med f g p1 p2 H) = p2;
  pull_med_unique {x y z v: C} (f: x ~> z) (g: y ~> z) (p1: v ~> x) (p2: v ~> y) (H: f ∘ p1 = g ∘ p2) (u: v ~> Pull f g): pull1 f g ∘ u = p1 -> pull2 f g ∘ u = p2 -> pull_med f g p1 p2 H = u;
}.

Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type := Pack { sort: Category; _: class_of sort }.
Local Coercion sort: type >-> Category.

Variable T: type.
Definition class := match T return class_of T with Pack _ c => c end.

Definition Cat: Cat := T.

End ClassDef.

Module Exports.

Coercion sort: type >-> Category.
Coercion Cat: type >-> Category.obj.
Notation PullCategory := type.

End Exports.

End PullCategory.

Export PullCategory.Exports.

Section Pullback.
Context {C: PullCategory}.

Definition Pull: forall {x y z: C}, x ~> z -> y ~> z -> C := @PullCategory.Pull C (PullCategory.class C).
Definition pull1: forall {x y z: C} (f: x ~> z) (g: y ~> z), Pull f g ~> x := @PullCategory.pull1 C (PullCategory.class C).
Definition pull2: forall {x y z: C} (f: x ~> z) (g: y ~> z), Pull f g ~> y := @PullCategory.pull2 C (PullCategory.class C).
Definition pull_comm: forall {x y z: C} (f: x ~> z) (g: y ~> z), f ∘ pull1 f g = g ∘ pull2 f g := @PullCategory.pull_comm C (PullCategory.class C).
Definition pull_med: forall {x y z v: C} (f: x ~> z) (g: y ~> z) (p1: v ~> x) (p2: v ~> y), f ∘ p1 = g ∘ p2 -> v ~> Pull f g := @PullCategory.pull_med C (PullCategory.class C).
Definition pull_med1: forall {x y z v: C} (f: x ~> z) (g: y ~> z) (p1: v ~> x) (p2: v ~> y) (H: f ∘ p1 = g ∘ p2), pull1 f g ∘ (pull_med f g p1 p2 H) = p1 := @PullCategory.pull_med1 C (PullCategory.class C).
Definition pull_med2: forall {x y z v: C} (f: x ~> z) (g: y ~> z) (p1: v ~> x) (p2: v ~> y) (H: f ∘ p1 = g ∘ p2), pull2 f g ∘ (pull_med f g p1 p2 H) = p2 := @PullCategory.pull_med2 C (PullCategory.class C).
Definition pull_med_unique: forall {x y z v: C} (f: x ~> z) (g: y ~> z) (p1: v ~> x) (p2: v ~> y) (H: f ∘ p1 = g ∘ p2) (u: v ~> Pull f g), pull1 f g ∘ u = p1 -> pull2 f g ∘ u = p2 -> pull_med f g p1 p2 H = u := @PullCategory.pull_med_unique C (PullCategory.class C).

End Pullback.
