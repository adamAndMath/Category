Require Export Sets.

Definition rel (X Y: set) := {R: set -> set -> Prop | forall x y, R x y -> x ∈ X /\ y ∈ Y}.

Lemma rel_eq {X Y: set} (R Q: rel X Y): R = Q <-> (forall x y, proj1_sig R x y <-> proj1_sig Q x y).
Proof.
  split; intro H.
  now subst Q.
  apply eq_sig.
  extensionality x.
  extensionality y.
  apply propositional_extensionality.
  apply H.
Qed.

Ltac rel_eq x y :=
  match goal with
  | [ |- ?R = ?Q] =>
    apply (rel_eq R Q);
    simpl;
    intros x y
  end.

Definition rel_id (X: set): rel X X.
Proof.
  unshelve eexists.
  exact (fun x y => x ∈ X /\ x = y).
  intros x y [Hx Hy].
  now subst y.
Defined.

Definition rel_comp {X Y Z: set} (R: rel Y Z) (Q: rel X Y): rel X Z.
Proof.
  unshelve eexists.
  exact (fun x z => exists y, proj1_sig R y z /\ proj1_sig Q x y).
  intros x z [y [yz xy]].
  split.
  apply (proj2_sig Q x y xy).
  apply (proj2_sig R y z yz).
Defined.

Lemma rel_comp_assoc (A B C D: set) (R: rel C D) (Q: rel B C) (P: rel A B): rel_comp R (rel_comp Q P) = rel_comp (rel_comp R Q) P.
Proof.
  rel_eq a d.
  split.
  + intros [c [cd [b [bc ab]]]].
    exists b; split.
    exists c; split.
    all: assumption.
  + intros [b [[c [cd bc]] ab]].
    1: exists c; split.
    2: exists b; split.
    all: assumption.
Qed.

Lemma rel_comp_id_l (X Y: set) (R: rel X Y): rel_comp (rel_id Y) R = R.
Proof.
  rel_eq a b.
  split.
  + intros [b' [[_ e] ab]].
    now subst b'.
  + intros ab.
    exists b.
    repeat split.
    apply (proj2_sig R a b ab).
    exact ab.
Qed.

Lemma rel_comp_id_r (X Y: set) (R: rel X Y): rel_comp R (rel_id X) = R.
Proof.
  rel_eq a b.
  split.
  + intros [a' [ab [_ e]]].
    now subst a'.
  + intros ab.
    exists a.
    repeat split.
    exact ab.
    apply (proj2_sig R a b ab).
Qed.

Definition REL_mixin: Category.mixin_of set :=
  Category.Mixin set rel rel_id (@rel_comp) rel_comp_assoc rel_comp_id_l rel_comp_id_r.

Definition REL: Category :=
  Category.Pack set REL_mixin.
