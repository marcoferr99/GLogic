From stdpp Require Import list sets.
Require Import g_stlc.


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
        has_type C a ty_prp ->
        tm_equiv |(C)| a b ->
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
        is_derivable (sq_build C (subst_last |(C)| t b :: l) c) ->
        is_derivable (sq_build C (<{for T, b}> :: l) c)
    | rl_forR C T l b sb :
        (forall t, t ∈ sb <-> t ∈ supp b) ->
        is_derivable (sq_build (C +: foldr ty_arr T (has_type_other <$> sb)) (sq_set_map (bound_level_map S |(C)|) l) (
          subst_last2 (S |(C)|) |(C)| (foldl tm_app (tm_lvl |(C)|) sb) b
        )) ->
        is_derivable (sq_build C l <{for T, b}>)
    | rl_exL C T l b c sb :
        (forall t, t ∈ sb <-> t ∈ supp b) ->
        is_derivable (sq_build (C +: foldr ty_arr T (has_type_other <$> sb)) ((
          subst_last2 (S |(C)|) |(C)| (foldl tm_app (tm_lvl |(C)|) sb) b
        ) :: (sq_set_map (bound_level_map S |(C)|) l)) (bound_level_map S |(C)| c)) ->
        is_derivable (sq_build C (<{ex T, b}> :: l) c)
    | rl_exR C T l b t :
        has_type C t T ->
        is_derivable (sq_build C l (subst_last |(C)| t b)) ->
        is_derivable (sq_build C l <{ex T, b}>)
    | rl_nabL C T l b c n :
        gtm_nom T n ∉ supp b ->
        is_derivable (sq_build C (subst_last |(C)| (gtm_nom T n) b :: l) c) ->
        is_derivable (sq_build C (<{nab T, b}> :: l) c)
    | rl_nabR C T l b n :
        gtm_nom T n ∉ supp b ->
        is_derivable (sq_build C l (subst_last |(C)| (gtm_nom T n) b)) ->
        is_derivable (sq_build C l (<{nab T, b}>))
  .

  Theorem th C T h l t :
    Forall2 (fun x X => has_type C x X) l h ->
    has_type C t (foldr ty_arr T h) ->
    has_type C (foldl tm_app t l) T.
  Proof.
    generalize dependent t. generalize dependent h.
    induction l; intros h t F Ht.
    - inversion F. now subst.
    - simpl. destruct h; inversion F. subst.
      eapply IHl; try eassumption.
      tm_simpl. exists t0. now split.
  Qed.

  Theorem is_derivable_wf K : is_derivable K -> wf_sequent K.
  Proof.
    intros D. induction D; simpl in *.
    - split.
      + eapply has_type_tm_equiv; eassumption.
      + intros t Ht.
        apply elem_of_singleton in Ht. now subst.
    - intuition. apply elem_of_union in H3 as [Ht | Ht]; [auto|].
      + apply H2. apply elem_of_union. now left.
    - intuition. apply H0. apply elem_of_union. now left.
    - intuition. set_unfold. destruct H2; [auto|].
      now subst.
    - intuition. set_unfold. subst. now constructor.
    - intuition.
      + now constructor.
      + now set_unfold.
    - intuition. set_unfold. destruct H3.
      + apply H0. intuition.
      + subst. econstructor; [econstructor|]; intuition.
        now apply ht_other2.
    - intuition. econstructor; [econstructor|]; try eassumption.
      now apply ht_other2.
    - intuition. econstructor; [econstructor|]; try eassumption.
      now apply ht_other2.
    - intuition. set_unfold. destruct H2; [intuition|].
      subst. econstructor; [econstructor|].
      + now apply ht_other2.
      + apply H1. intuition.
      + assumption.
    - intuition. set_unfold. destruct H2; [intuition|].
      subst. econstructor; [econstructor|].
      + now apply ht_other2.
      + assumption.
      + apply H1. intuition.
    - intuition. econstructor; [econstructor|]; try eassumption.
      now apply ht_other2.
    - intuition. set_unfold. destruct H3; intuition.
      subst. econstructor; [econstructor|].
      + now apply ht_other2.
      + assumption.
      + apply H2. intuition.
    - intuition.
      + econstructor; [econstructor|].
        * now apply ht_other2.
        * apply H0. set_unfold. intuition.
        * assumption.
      + apply H0. set_unfold. intuition.
    - intuition. set_unfold. destruct H2.
      + apply H1. intuition.
      + subst. econstructor.
        * now apply ht_other2.
        * tm_simpl. exists ty_prp. split; [|reflexivity].
          eapply has_type_subst_last; eauto.
    - intuition; [econstructor|].
      + now apply ht_other2.
      + tm_simpl. exists ty_prp. intuition.
        eapply (has_type_subst_last2_2 _ (C +: foldr ty_arr T (has_type_other <$> sb))).
        4:{ rewrite rlength_rcons. eassumption. }
        * now rewrite rlength_rcons.
        * intros. now rewrite lookup_rcons_lt.
        * clear D H0 H1.
          eapply th.
          2:{
            tm_simpl. now rewrite @lookup_rcons_eq.
          }
          remember (C +: foldr ty_arr T (has_type_other <$> sb)) as D.
          clear HeqD.
          assert (forall t, t ∈ sb -> t ∈ supp b). { intros. now apply H. }
          clear H.
          induction sb.
          -- simpl. constructor.
          -- simpl in *. constructor.
             ++ constructor. eapply supp_other. apply H0. set_unfold. intuition.
             ++ apply IHsb. intros. apply H0. set_unfold. intuition.
      + eapply (has_type_bound_level_map2 1).
        3:{
          specialize H1 with (bound_level_map S |(C)| t0).
          unfold bound_level_map in *. erewrite level_map_f_eq.
          - apply H1. apply sq_set_map_spec. exists t0. now split.
          - simpl. now intros n.
        }
        * apply rlength_rcons.
        * intros n Hn. now apply lookup_rcons_lt.
    - set_unfold. intuition.
      + eapply (has_type_bound_level_map2 1); try eassumption.
        * apply rlength_rcons.
        * intros n Hn. now apply lookup_rcons_lt.
      + eapply (has_type_bound_level_map2 1).
        3:{
          specialize H1 with (bound_level_map S |(C)| x).
          unfold bound_level_map in *. erewrite level_map_f_eq.
          - apply H1. left. apply sq_set_map_spec. exists x. intuition.
          - intros. now simpl.
        }
        * apply rlength_rcons.
        * intros n Hn. now apply lookup_rcons_lt.
      + subst. econstructor; [now apply ht_other2|].
        tm_simpl. exists ty_prp. intuition.
        eapply (has_type_subst_last2_2 _ (C +: foldr ty_arr T (has_type_other <$> sb))).
        4:{ rewrite rlength_rcons. apply H1. now right. }
        * now rewrite rlength_rcons.
        * intros. symmetry. now apply lookup_rcons_lt.
        * clear D H0 H1.
          eapply th.
          2:{
            tm_simpl. now rewrite @lookup_rcons_eq.
          }
          remember (C +: foldr ty_arr T (has_type_other <$> sb)) as D.
          clear HeqD.
          assert (forall t, t ∈ sb -> t ∈ supp b). { intros. now apply H. }
          clear H.
          induction sb.
          -- simpl. constructor.
          -- simpl in *. constructor.
             ++ constructor. eapply supp_other. apply H0. set_unfold. intuition.
             ++ apply IHsb. intros. apply H0. set_unfold. intuition.
    - intuition. econstructor; [now apply ht_other2|].
      tm_simpl. exists ty_prp. split; [|easy].
      eapply has_type_subst_last; eauto.
    - intuition. set_unfold. destruct H2.
      + apply H1. intuition.
      + subst. econstructor; [now apply ht_other2|].
        tm_simpl. eexists. split; [|reflexivity].
        eapply has_type_subst_last.
        2:{ apply H1. now right. }
        now constructor.
    - intuition. econstructor; [now apply ht_other2|].
      tm_simpl. eexists. split; [|reflexivity].
      eapply has_type_subst_last; try eassumption.
      now constructor.
  Qed.
End GLogic.
