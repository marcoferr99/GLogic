Require Export glogic.

Theorem example1 C l T B :
  [{ C ; l --> (∇ T, ~ B) ≡ ~ (∇ T, B) }].
Proof.
  destruct (nom_in_supp B T) as [a Ha].
  constructor; constructor.
  - apply (rl_nabL _ a); tm_simpl.
    { assumption. }
    apply contrapositive.
    apply (rl_nabL _ a Ha). apply rl_id2.
  - apply (rl_nabR _ a); tm_simpl.
    { assumption. }
    apply contrapositive.
    apply (rl_nabR _ a Ha). apply rl_id2.
Qed.

Theorem example2 C l T b c :
  [{ C; l --> (∇ T, b \/ c) ≡ (∇ T, b) \/ (∇ T, c) }].
Proof.
  destruct (nom_in_supp <{ b \/ c }> T) as [n Hn].
  constructor; constructor.
  - apply (rl_nabL _ n) > [easy|].
    tm_simpl. apply rl_orL.
    + apply rl_orR1. apply (rl_nabR _ n).
      * unfold in_supp in *. simpl in *. intuition.
      * apply rl_id2.
    + apply rl_orR2. apply (rl_nabR _ n).
      * unfold in_supp in *. simpl in *. intuition.
      * apply rl_id2.
  - apply (rl_nabR _ n) > [easy|].
    tm_simpl. apply rl_orL.
    + apply rl_orR1. apply (rl_nabL _ n).
      * unfold in_supp in *. simpl in *. intuition.
      * apply rl_id2.
    + apply rl_orR2. apply (rl_nabL _ n).
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

Definition ex4_clause_f (l : list ty) n :=
  match l, n with
  | [], 0 => Some (def_ind, <{\: ty_prp, 0}>)
  | _, _ => None
  end.

Theorem example4 C :
  ({ ex4_clause_f; C; $({[gtm_prd [] 0]}) --> gtm_bot }).
Proof.
  assert ( {[gtm_prd [] 0]} ≡ (∅ +; foldl tm_app (gtm_prd [] 0) [] : tm_set)).
  - simpl. symmetry. apply union_empty.
  - rewrite H.
   eapply (rl_iL _ _ _ _ _ _ gtm_bot).
    + simpl. reflexivity.
    + simpl. intros. has_type.
    + simpl. rewrite <- union_empty. apply rl_id.
      apply tm_equiv_id.
      apply rtsc_lr. simpl.
      apply step_conv. left.
      constructor.
    + simpl. apply rl_id2.
  Qed.

Definition ex5_clause_f (l : list ty) n :=
  match l, n with
  | [], 0 => Some (def_cin, <{\: ty_prp, 0}>)
  | _, _ => None
  end.

Theorem example5 C :
  ({ ex5_clause_f; C; ∅ --> $(gtm_prd [] 0) }).
Proof.
  change (gtm_prd [] 0) with (foldl tm_app (gtm_prd [] 0) []).
  eapply (rl_ciR _ _ _ _ _ _ gtm_top); simpl.
  - reflexivity.
  - intros. has_type.
  - rewrite <- union_empty. apply rl_id.
    apply tm_equiv_id. apply rtsc_rl. simpl.
    apply step_conv. left. constructor.
  - constructor.
Qed.
