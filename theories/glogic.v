Require Export g_stlc.
From stdpp Require Import sets.
Close Scope list_scope.


(*************************)
(** * G Logic Deductions *)
(*************************)

Module Type SQ_SET.
  Import GStlc.

  Parameter sq_set : Set.
  Declare Instance sq_set_elem_of : ElemOf tm sq_set.
  Declare Instance sq_set_empty : Empty sq_set.
  Declare Instance sq_set_singleton : Singleton tm sq_set.
  Declare Instance sq_set_union : Union sq_set.
  Declare Instance sq_set_semi_set : SemiSet _ sq_set.
  Parameter sq_set_map : (tm -> tm) -> sq_set -> sq_set.
  Axiom sq_set_map_spec :
    forall f s t, t ∈ sq_set_map f s <-> exists a, a ∈ s /\ t = f a.
End SQ_SET.

Notation "x :: X" := (X ∪ {[x]}) : stlc_scope.

Module GLogic (SqSet : SQ_SET).
  Export SqSet.
  Export GStlcTheories.

  Record sequent : Type := sq_build {
    sq_context : context;
    sq_premises : sq_set;
    sq_conclusion : tm
  }.

  Definition wf_sequent s :=
    match s with
    | sq_build C p j => has_type C j ty_prp /\ forall t, t ∈ p -> has_type C t ty_prp
    end.

  (*Notation "|( sig ; l --> B )|" := (sq_build sig l B)
    (sig custom stlc_ty, l custom stlc_ty, B custom stlc_ty).*)

  Inductive is_derivable : sequent -> Prop :=
    | rl_id C a b :
        has_type C a ty_prp -> tm_equiv C a b ->
        is_derivable (sq_build C {[a]} b)
    | rl_cut C l m b c :
        is_derivable (sq_build C l b) ->
        is_derivable (sq_build C (b :: m) c) ->
        is_derivable (sq_build C (l ∪ m) c)
    | rl_cL C l b c :
        is_derivable (sq_build C (b :: b :: l) c) ->
        is_derivable (sq_build C (b :: l) c)
    | rl_wL C l b a :
        has_type C a ty_prp ->
        is_derivable (sq_build C l b) ->
        is_derivable (sq_build C (a :: l) b)
    | rl_botL C c :
        has_type C c ty_prp ->
        is_derivable (sq_build C {[gtm_bot]} c)
    | rl_topR C :
        is_derivable (sq_build C ∅ gtm_top)
    | rl_orL C l b c d :
        is_derivable (sq_build C (b :: l) c) ->
        is_derivable (sq_build C (d :: l) c) ->
        is_derivable (sq_build C (<{ b \/ d }> :: l) c)
    | rl_orR1 C l b c :
        has_type C c ty_prp ->
        is_derivable (sq_build C l b) ->
        is_derivable (sq_build C l <{ b \/ c }>)
    | rl_orR2 C l b c :
        has_type C b ty_prp ->
        is_derivable (sq_build C l c) ->
        is_derivable (sq_build C l <{ b \/ c }>)
    | rl_andL1 C l b c d :
        has_type C d ty_prp ->
        is_derivable (sq_build C (b :: l) c) ->
        is_derivable (sq_build C (<{ b /\ d }> :: l) c)
    | rl_andL2 C l b c d :
        has_type C b ty_prp ->
        is_derivable (sq_build C (d :: l) c) ->
        is_derivable (sq_build C (<{ b /\ d }> :: l) c)
    | rl_andR C l b c :
        is_derivable (sq_build C l b) ->
        is_derivable (sq_build C l c) ->
        is_derivable (sq_build C l <{ b /\ c }>)
    | rl_impL C l b c d :
        is_derivable (sq_build C l b) ->
        is_derivable (sq_build C (d :: l) c) ->
        is_derivable (sq_build C (<{ b > d }> :: l) c)
    | rl_impR C l b c :
        is_derivable (sq_build C (b :: l) c) ->
        is_derivable (sq_build C l <{ b > c }>)
    | rl_forL C T l b c t :
        has_type C t T ->
        is_derivable (sq_build C (subst_last C C t b :: l) c) ->
        is_derivable (sq_build C (<{for T, b}> :: l) c)
    | rl_forR C T l b sb :
        (forall t, t ∈ sb <-> in_supp b t) ->
        is_derivable (sq_build (C +: foldr ty_arr T (type_check_other <$> sb)) (sq_set_map (lift C) l) (
          subst_last C (S C) (foldl tm_app (tm_lvl C) sb) b
        )) ->
        is_derivable (sq_build C l <{for T, b}>)
    | rl_exL C T l b c sb :
        (forall t, t ∈ sb <-> in_supp b t) ->
        is_derivable (sq_build (C +: foldr ty_arr T (type_check_other <$> sb)) ((
          subst_last C (S C) (foldl tm_app (tm_lvl C) sb) b
        ) :: (sq_set_map (lift C) l)) (lift C c)) ->
        is_derivable (sq_build C (<{ex T, b}> :: l) c)
    | rl_exR C T l b t :
        has_type C t T ->
        is_derivable (sq_build C l (subst_last C C t b)) ->
        is_derivable (sq_build C l <{ex T, b}>)
    | rl_nabL C T l b c n :
        ~ in_supp b (gtm_nom T n) ->
        is_derivable (sq_build C (subst_last C C (gtm_nom T n) b :: l) c) ->
        is_derivable (sq_build C (<{nab T, b}> :: l) c)
    | rl_nabR C T l b n :
        ~ in_supp b (gtm_nom T n) ->
        is_derivable (sq_build C l (subst_last C C (gtm_nom T n) b)) ->
        is_derivable (sq_build C l (<{nab T, b}>))
  .


  Theorem has_type_fold C T h l t :
    Forall2 (fun x X => has_type C x X) l h ->
    has_type C t (foldr ty_arr T h) ->
    has_type C (foldl tm_app t l) T.
  Proof.
    revert h t. induction l; intros h t F Ht.
    - inversion F. now subst.
    - simpl. destruct h; inversion F. subst.
      eapply IHl; try eassumption.
      tm_simpl. now exists t0.
  Qed.

  Theorem has_type_fold2 C T sb b :
    (forall t, t ∈ sb -> in_supp b t) ->
    has_type (C +: foldr ty_arr T (type_check_other <$> sb)) (subst_last C (S C) (foldl tm_app (tm_lvl C) sb) b) -[ o ]- ->
    has_type (C +: T) b ty_prp.
  Proof.
    intros.
    eapply (has_type_subst_last2 _ (C +: foldr ty_arr T (type_check_other <$> sb)));
      simpl; try eassumption; try lia.
    - intros. now rewrite decide_True.
    - eapply has_type_fold; tm_simpl; [|rewrite decide_False; intuition lia].
      remember (C +: foldr ty_arr T (type_check_other <$> sb)) as D eqn : ED.
      clear ED H0. induction sb; simpl in *; constructor.
      + constructor. set_unfold. eapply in_supp_other. auto.
      + set_unfold. auto.
  Qed.

  Theorem is_derivable_wf K : is_derivable K -> wf_sequent K.
  Proof.
    intros D. induction D; simpl in *.
    - split.
      + eapply has_type_tm_equiv; eassumption.
      + intros. set_unfold. congruence.
    - set_unfold. intuition.
    - set_unfold. intuition.
    - set_unfold. intuition. congruence.
    - set_unfold. intuition. subst. now constructor.
    - set_unfold. intuition. now constructor.
    - set_unfold. intuition. subst.
      repeat eapply ht_app; auto. now apply ht_other2.
    - intuition. repeat eapply ht_app; try eassumption. now apply ht_other2.
    - intuition. repeat eapply ht_app; try eassumption. now apply ht_other2.
    - set_unfold. intuition. subst.
      repeat eapply ht_app; eauto. now apply ht_other2.
    - set_unfold. intuition. subst.
      repeat eapply ht_app; eauto. now apply ht_other2.
    - intuition. repeat eapply ht_app; try eassumption. now apply ht_other2.
    - set_unfold. intuition. subst.
      repeat eapply ht_app; eauto. now apply ht_other2.
    - set_unfold. intuition.
      repeat eapply ht_app; eauto. now apply ht_other2.
    - set_unfold. intuition. subst. econstructor.
      + now apply ht_other2.
      + tm_simpl. eexists; try reflexivity.
        eapply has_type_subst_last2; eauto.
    - intuition; [econstructor|].
      + now apply ht_other2.
      + tm_simpl. eexists; intuition.
        eapply has_type_fold2; try eassumption. apply H.
      + eapply has_type_lift2.
        apply H1. apply sq_set_map_spec. eauto.
    - set_unfold. intuition.
      + eapply has_type_lift2; eassumption.
      + eapply has_type_lift2. apply H1. left.
        apply sq_set_map_spec. eauto.
      + subst. econstructor; [now apply ht_other2|].
        tm_simpl. eexists; try reflexivity.
        eapply has_type_fold2; auto. apply H.
    - intuition. econstructor; [now apply ht_other2|].
      tm_simpl. eexists; [|reflexivity].
      eapply has_type_subst_last2; eauto.
    - set_unfold. intuition. subst.
      econstructor; [now apply ht_other2|].
      tm_simpl. eexists; [|reflexivity].
      eapply has_type_subst_last2; eauto.
      now constructor.
    - intuition. econstructor; [now apply ht_other2|].
      tm_simpl. eexists; [|reflexivity].
      eapply has_type_subst_last2; eauto.
      now constructor.
  Qed.
End GLogic.
