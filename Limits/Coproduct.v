Require Export Limits.Product.

Lemma coprod_limit (C: Category): ex_colim ((1: Category) + 1) C <-> inhabited (CoprodCategory.mixin_of C).
Proof.
  rewrite <- ex_lim_co.
  rewrite co_plus, co_1.
  rewrite prod_limit.
  split.
  all: intros [m].
  all: constructor.
  apply CoprodCo_mixin, m.
  apply (CoProd_mixin (CoprodCategory.Pack C m)).
Qed.
