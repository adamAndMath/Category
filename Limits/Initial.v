Require Export Limits.Terminal.

Lemma bot_limit (C: Category): ex_colim 0 C <-> inhabited (BotCategory.mixin_of C).
Proof.
  rewrite <- ex_lim_co.
  rewrite (proj2 (iso_0 (co 0))).
  rewrite top_limit.
  split.
  1, 2: intros [m].
  all: constructor.
  apply BotCo_mixin, m.
  apply (CoTop_mixin (BotCategory.Pack C m)).
  apply coZero2Zero.
Qed.
