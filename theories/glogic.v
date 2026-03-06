From stdpp Require Import list.
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
        is_derivable (sq_build (C +: foldr ty_arr T (has_type_other <$> sb)) l (
          subst_last (S |(C)|) (foldl tm_app (tm_lvl |(C)|) sb) b
        )) ->
        is_derivable (sq_build C l <{for T, b}>)
    | rl_exL C T l b c sb :
        (forall t, t ∈ sb <-> t ∈ supp b) ->
        is_derivable (sq_build (C +: foldr ty_arr T (has_type_other <$> sb)) ((
          subst_last (S |(C)|) (foldl tm_app (tm_lvl |(C)|) sb) b
        ) :: l) c) ->
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

  (*
  Theorem is_derivable_wf K : is_derivable K -> wf_sequent K.
  Proof.
    intros D. induction D; simpl in *; intuition;
    try solve [
      try match goal with
        [H : _ |- _] => inversion H; clear H; subst
      end; try assumption;
      repeat econstructor; eassumption
    ].
    - inversion H2. now apply Forall_app.
    - inversion H0. inversion H2. subst.
      repeat (econstructor; try eassumption).
    - inversion H1. subst. clear H1.
      constructor; [|assumption]. clear D H5 H0.
      econstructor; constructor.
      eapply has_type_subst2; try eassumption;
        [repeat rewrite length_app; simpl; lia|].
      apply Forall2_app; [|repeat constructor; assumption].
      unfold lvl_seq at 2. simpl. rewrite app_nil_r.
      generalize (has_type_seq [] (C ++ c) []).
      rewrite app_nil_r. simpl. auto.
    - econstructor; constructor.
      eapply has_type_subst2.
      3:{
        replace (|(C ++ c)| + 1) with
          |(C +: foldr ty_arr S c ++ c)| in H;
          [|repeat rewrite length_app; simpl; lia].
        apply H.
      }
      + repeat rewrite length_app. simpl. lia.
      + repeat apply Forall2_app.
        * generalize (has_type_seq []). intros HS.
          simpl in HS. rewrite <- app_assoc. apply HS.
        * generalize (has_type_seq (C +: foldr ty_arr S c) c []).
          rewrite length_app. rewrite app_nil_r.
          simpl. intros HS. apply HS.
        * repeat constructor.
          clear dependent l s.
          induction c.
          -- simpl. constructor.
             replace (C +: S ++ []) with (C ++ S :: []);
               [|symmetry; apply app_nil_r].
             now apply list_lookup_middle.
          -- simpl.
             Search lookup length.
          eapply has_type_subst2.
          inversion H0; subst.
          -- destruct D.
      + apply (has_type_seq []).
      unfold wf_judgement in *.
      eapply has_type_subst_ind2.
      unfold subst_ind in *. rewrite Nat.add_0_r in H4.
      eapply has_type_subst2 in H4; try eassumption.
      + repeat rewrite length_app. simpl. lia.
      + apply Forall2_app.
        * remember (C0 ++ c) as L.
          clear dependent C0. clear H.
          assert (F : forall n, Forall2 (fun (si : tm) (Si : ty) => <| L |- si : Si |>) (map tm_lvl (seq n (length L))) L); [|apply F].
          replace L with (rev (rev L));
            [|apply rev_involutive].
          remember (rev L) as m. clear dependent L.
          induction m; [constructor|].
          intros n. simpl.
          rewrite length_app. rewrite seq_app. simpl.
          rewrite map_app. simpl.
          apply Forall2_app.
          --
          replace (length (a :: L)) with (S (length L));
            [|reflexivity].
          intros n. simpl. constructor.
          rewrite seq_S. simpl.
          simpl. constructor.
  Qed.
  *)
End GLogic.
