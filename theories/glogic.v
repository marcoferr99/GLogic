Require Import stlc.


(*************************)
(** * G Logic Deductions *)
(*************************)

Module GLogic (Ty : TY).
  Module Stlc := Stlc Ty.
  Import Stlc.

  Record judgement : Set := jd_build {
    jd_cnt : context;
    jd_tm  : tm
  }.

  Definition wf_judgement C j :=
    match j with | jd_build c t => has_type (C ++ c) t ty_prp end.

  Record sequent : Set := sq_build {
    sq_context : context;
    sq_premises : list judgement;
    sq_conclusion : judgement
  }.

  Definition wf_sequent s :=
    match s with
    | sq_build C l j => wf_judgement C j /\ Forall (wf_judgement C) l
    end.

  (*Notation "|( sig ; l --> B )|" := (sq_build sig l B)
    (sig custom stlc_ty, l custom stlc_ty, B custom stlc_ty).*)
  Notation "c :> t" := (jd_build c t)
    (at level 70, t custom stlc_tm at level 60) : stlc_scope.

  Inductive is_derivable : sequent -> Prop :=
    | rl_init C c t :
        has_type (C ++ c) t ty_prp ->
        is_derivable (sq_build C [c :> t] (c :> t))
    | rl_cut C l m b c :
        is_derivable (sq_build C l b) ->
        is_derivable (sq_build C (b :: m) c) ->
        is_derivable (sq_build C (l ++ m) c)
    | rl_cL C l b c :
        is_derivable (sq_build C (b :: b :: l) c) ->
        is_derivable (sq_build C (b :: l) c)
    | rl_wL C c l b t :
        has_type (C ++ c) t ty_prp ->
        is_derivable (sq_build C l b) ->
        is_derivable (sq_build C ((c :> t) :: l) b)
    | rl_botL C c d t :
        has_type (C ++ c) t ty_prp ->
        is_derivable (sq_build C [d :> tm_bot] (c :> t))
    | rl_topR C c :
        is_derivable (sq_build C [] (c :> tm_top))
    | rl_andL1 C c l b t s :
        has_type (C ++ c) t ty_prp ->
        is_derivable (sq_build C ((c :> s) :: l) b) ->
        is_derivable (sq_build C ((c :> tm_and s t) :: l) b)
    | rl_andL2 C c l b t s :
        has_type (C ++ c) s ty_prp ->
        is_derivable (sq_build C ((c :> t) :: l) b) ->
        is_derivable (sq_build C ((c :> tm_and s t) :: l) b)
    | rl_andR C c l t s :
        is_derivable (sq_build C l (c :> s)) ->
        is_derivable (sq_build C l (c :> t)) ->
        is_derivable (sq_build C l (c :> tm_and s t))
    | rl_orL C c l b t s :
        is_derivable (sq_build C (c :> s :: l) b) ->
        is_derivable (sq_build C (c :> t :: l) b) ->
        is_derivable (sq_build C ((c :> tm_or s t) :: l) b)
    | rl_orR1 C c l t s :
        has_type (C ++ c) t ty_prp ->
        is_derivable (sq_build C l (c :> s)) ->
        is_derivable (sq_build C l (c :> tm_or s t))
    | rl_orR2 C c l t s :
        has_type (C ++ c) s ty_prp ->
        is_derivable (sq_build C l (c :> t)) ->
        is_derivable (sq_build C l (c :> tm_or s t))
    | rl_impL C c l B t s :
        is_derivable (sq_build C l (c :> s)) ->
        is_derivable (sq_build C ((c :> t) :: l) B) ->
        is_derivable (sq_build C ((c :> tm_imp s t) :: l) B)
    | rl_impR C c l t s :
        is_derivable (sq_build C ((c :> s) :: l) (c :> t)) ->
        is_derivable (sq_build C l (c :> tm_imp s t))
    | rl_forL C c T l B t s :
        has_type (C ++ c) t T ->
        is_derivable (sq_build C
          ((c :> $(subst_ind |(C ++ c)| |(C ++ c)| 0 t s)) :: l) B) ->
        is_derivable (sq_build C ((c :> for T, s) :: l) B)
    | rl_forR C c S l s :
        is_derivable (sq_build (C +: foldr ty_arr S c) l (c :> $(
          subst_ind (|(C ++ c)| + 1) |(C)| |(c)|
            (foldl tm_app (tm_lvl |(C)|) (lvl_seq (|(C)| + 1) |(c)|)) s
        ))) ->
        is_derivable (sq_build C l (c :> for S, s))
    | rl_exL C c S l B s :
        is_derivable (sq_build (C +: foldr ty_arr S c) ((c :> $(
          subst_ind (|(C ++ c)| + 1) |(C)| |(c)|
            (foldl tm_app (tm_lvl |(C)|) (lvl_seq (|(C)| + 1) |(c)|)) s
        )) :: l) B) ->
        is_derivable (sq_build C ((c :> ex S, s) :: l) B)
    | rl_exR C c T l t s :
        has_type (C ++ c) t T ->
        is_derivable (sq_build C l (c :> $(subst_ind |(C ++ c)| |(C ++ c)| 0 t s))) ->
        is_derivable (sq_build C l (c :> ex T, s))
  .

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
End GLogic.
