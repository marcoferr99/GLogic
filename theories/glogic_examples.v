Require Export glogic.

Theorem example1 C l T B :
  [{ C ; l --> (∇ T, ~ B) ≡ ~ (∇ T, B) }].
Proof.
  destruct (nom_in_supp B T) as [a Ha].
  constructor; constructor.
  - apply (rl_nabL a); tm_simpl.
    { assumption. }
    apply contrapositive. apply (rl_nabL a Ha).
    apply rl_id2.
  - apply (rl_nabR a); tm_simpl.
    { assumption. }
    apply contrapositive. apply (rl_nabR a Ha).
    apply rl_id2.
Qed.

Theorem example2 C l T b c :
  [{ C; l --> (∇ T, b \/ c) ≡ (∇ T, b) \/ (∇ T, c) }].
Proof.
  destruct (nom_in_supp <{ b \/ c }> T) as [n Hn].
  constructor; constructor.
  - apply (rl_nabL n) > [easy|].
    tm_simpl. apply rl_orL.
    + apply rl_orR1. apply (rl_nabR n).
      * unfold in_supp in *. simpl in *. intuition.
      * apply rl_id2.
    + apply rl_orR2. apply (rl_nabR n).
      * unfold in_supp in *. simpl in *. intuition.
      * apply rl_id2.
  - apply (rl_nabR n) > [easy|].
    tm_simpl. apply rl_orL.
    + apply rl_orR1. apply (rl_nabL n).
      * unfold in_supp in *. simpl in *. intuition.
      * apply rl_id2.
    + apply rl_orR2. apply (rl_nabL n).
      * unfold in_supp in *. simpl in *. intuition.
      * apply rl_id2.
Qed.

(*
Theorem example3 C T t :
  ~ [{ C; ∅ --> ∇ T, ∇ T, t 0 1 > ∇ T, t 0 0 }].
Proof.
  intros H.
  remember <{ ∇ T, ∇ T, t 0 1 > (∇ T, t 0 0) }> as x. remember ∅ as e.
  assert (E : e ≡ ∅) by (now (rewrite Heqe)).
  clear Heqe.
  induction H; subst.
  - apply IHis_derivable.
    + reflexivity.
    + now rewrite H.
  - set_solver.
  - apply IHis_derivable1.
    + assert (m ≡ ∅) by set_solver.
      rewrite H2 in H1. inversion H1.
      *)
