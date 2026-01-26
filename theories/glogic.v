Require Import stlc.
Require Import Lia.


(*************************)
(** * G Logic Deductions *)
(*************************)

Module GLogic (Ty : TY).
  Module Stlc := Stlc Ty.
  Import Stlc.

  Record judgement : Set := {
    jd_context : context;
    jd_tm : tm
  }.

  Definition wf_judgement C j :=
    match j with
    | Build_judgement c t => has_type (C ++ c) t ty_prp
    end.

  Record sequent : Set := {
    sq_context : context;
    sq_premises : list judgement;
    sq_conclusion : judgement
  }.

  Definition wf_sequent s :=
    match s with
    | Build_sequent C l j => wf_judgement C j /\ Forall (wf_judgement C) l
    end.

  Notation "|( sig ; l --> B )|" := (Build_sequent sig l B)
    (sig custom stlc_ty, l custom stlc_ty, B custom stlc_ty).
  Notation "c :> t" := (Build_judgement c t)
    (at level 70, t custom stlc_tm at level 60) : stlc_scope.

  Inductive is_derivable : sequent -> Prop :=
    | rl_init C c t :
        has_type (C ++ c) t ty_prp ->
        is_derivable (Build_sequent C [c :> t] (c :> t))
    | rl_cut C l m b c :
        is_derivable (Build_sequent C l b) ->
        is_derivable (Build_sequent C (b :: m) c) ->
        is_derivable (Build_sequent C (l ++ m) c)
    | rl_cL C l b c :
        is_derivable (Build_sequent C (b :: b :: l) c) ->
        is_derivable (Build_sequent C (b :: l) c)
    | rl_wL C c l b t :
        has_type (C ++ c) t ty_prp ->
        is_derivable (Build_sequent C l b) ->
        is_derivable (Build_sequent C (c :> t :: l) b)
    | rl_botL C c d t :
        has_type (C ++ c) t ty_prp ->
        is_derivable (Build_sequent C [d :> tm_bot] (c :> t))
    | rl_topR C c :
        is_derivable (Build_sequent C [] (c :> tm_top))
    | rl_andL1 C c l b t s :
        has_type (C ++ c) t ty_prp ->
        is_derivable (Build_sequent C (c :> s :: l) b) ->
        is_derivable (Build_sequent C (c :> (tm_and s t) :: l) b)
    | rl_andL2 C c l b t s :
        has_type (C ++ c) s ty_prp ->
        is_derivable (Build_sequent C (c :> t :: l) b) ->
        is_derivable (Build_sequent C (c :> (tm_and s t) :: l) b)
    | rl_andR C c l t s :
        is_derivable (Build_sequent C l (c :> s)) ->
        is_derivable (Build_sequent C l (c :> t)) ->
        is_derivable (Build_sequent C l (c :> tm_and s t))
    | rl_orL C c l b t s :
        is_derivable (Build_sequent C (c :> s :: l) b) ->
        is_derivable (Build_sequent C (c :> t :: l) b) ->
        is_derivable (Build_sequent C (c :> tm_or s t :: l) b)
    | rl_orR1 C c l t s :
        has_type (C ++ c) t ty_prp ->
        is_derivable (Build_sequent C l (c :> s)) ->
        is_derivable (Build_sequent C l (c :> tm_or s t))
    | rl_orR2 C c l t s :
        has_type (C ++ c) s ty_prp ->
        is_derivable (Build_sequent C l (c :> t)) ->
        is_derivable (Build_sequent C l (c :> tm_or s t))
    | rl_impL C c l B t s :
        is_derivable (Build_sequent C l (c :> s)) ->
        is_derivable (Build_sequent C (c :> t :: l) B) ->
        is_derivable (Build_sequent C ((c :> tm_imp s t) :: l) B)
    | rl_impR C c l t s :
        is_derivable (Build_sequent C (c :> s :: l) (c :> t)) ->
        is_derivable (Build_sequent C l (c :> tm_imp s t))
    | rl_forL C c T l B s :
        has_type (C ++ c) t T ->
        is_derivable (Build_sequent C ((c :> $(subst (length (C ++ c)) (map tm_lvl (seq 0 (length (C ++ c))) ++ [t]) s)) :: l) B) ->
        is_derivable (Build_sequent C (c :> $(tm_for T) $(tm_abs T s) :: l) B)
  .

  Theorem th K : is_derivable K -> wf_sequent K.
  Proof.
    intros D. induction D; simpl in *.
    - split; [assumption|].
      constructor; [assumption|constructor].
    - destruct IHD2. split; [assumption|].
      apply Forall_app. split; [intuition|].
      now inversion H0.
    - destruct IHD. split; [assumption|].
      now inversion H0.
    - destruct IHD. split; [assumption|].
      constructor; assumption.
    - split; [assumption|].
      repeat constructor.
    - split; constructor.
    - destruct IHD. split; [assumption|].
      inversion H1. subst. constructor; [|assumption].
      simpl. econstructor; [|eassumption].
      econstructor; [constructor|assumption].
    - destruct IHD. split; [assumption|].
      inversion H1; subst. constructor; [|assumption].
      simpl. econstructor; [|eassumption].
      econstructor; [constructor|assumption].
    - intuition.
      econstructor; [|eassumption].
      econstructor; [constructor|assumption].
    - intuition.
      inversion H0. inversion H2. subst.
      constructor; [|assumption].
      econstructor; [|eassumption].
      econstructor; [constructor|assumption].
    - intuition.
      econstructor; [|eassumption].
      econstructor; [constructor|assumption].
    - intuition.
      econstructor; [|eassumption].
      econstructor; [constructor|assumption].
    - intuition.
      inversion H2. subst.
      constructor; [|assumption].
      econstructor; [|eassumption].
      econstructor; [constructor|assumption].
    - destruct IHD. inversion H0. subst.
      intuition.
      econstructor; [|eassumption].
      econstructor; [constructor|assumption].
    - intuition. inversion H1. subst.
      constructor; [|assumption].
      econstructor; constructor.
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
