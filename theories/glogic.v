Require Export g_stlc.
From stdpp Require Import sets.


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

(*
Notation "x :: X" := (X ∪ {[x]}) : stlc_scope.
Notation "X :: x" := (X ∪ {[x]}) (in custom stlc_tm at level 60, left associativity) : stlc_scope.
*)

Module GLogic (SqSet : SQ_SET).
  Export SqSet.
  Export GStlcTheories.

  (*
  Record sequent : Type := sq_build {
    sq_context : context;
    sq_premises : sq_set;
    sq_conclusion : tm;
    _ : forall t, t ∈ sq_premises -> has_type sq_context t ty_prp;
    _ : has_type sq_context sq_conclusion ty_prp
  }.
  *)

  Definition is_form C t := has_type C t ty_prp.
  Definition wf_sq_set C (l : sq_set) := forall t, t ∈ l -> has_type C t ty_prp.

  Definition wf_sequent C (p : sq_set) c := wf_sq_set C p /\ is_form C c.

  Inductive is_derivable_wf : context -> sq_set -> tm -> Prop :=
    | wrl_set C l m c :
        l ≡ m ->
        is_derivable_wf C l c ->
        is_derivable_wf C m c
    | wrl_id C a b :
        has_type C a ty_prp ->
        has_type C b ty_prp ->
        tm_equiv C a b ->
        is_derivable_wf C {[a]} b
    | wrl_cut C l m b c :
        is_derivable_wf C l b ->
        is_derivable_wf C (m ∪ {[b]}) c ->
        is_derivable_wf C (l ∪ m) c
    | wrl_cL C l b c :
        is_derivable_wf C (l ∪ {[b; b]}) c ->
        is_derivable_wf C (l ∪ {[b]}) c
    | wrl_wL C l m b :
        (forall a, a ∈ l -> has_type C a ty_prp) ->
        is_derivable_wf C m b ->
        is_derivable_wf C (l ∪ m) b
    | wrl_botL C c :
        has_type C c ty_prp ->
        is_derivable_wf C {[gtm_bot]} c
    | wrl_topR C :
        is_derivable_wf C ∅ gtm_top
    | wrl_orL C l b c d :
        is_derivable_wf C (l ∪ {[b]}) c ->
        is_derivable_wf C (l ∪ {[d]}) c ->
        is_derivable_wf C (l ∪ {[ <{ b \/ d }> ]}) c
    | wrl_orR1 C l b c :
        has_type C c ty_prp ->
        is_derivable_wf C l b ->
        is_derivable_wf C l <{ b \/ c }>
    | wrl_orR2 C l b c :
        has_type C b ty_prp ->
        is_derivable_wf C l c ->
        is_derivable_wf C l <{ b \/ c }>
    | wrl_andL1 C l b c d :
        has_type C d ty_prp ->
        is_derivable_wf C (l ∪ {[b]}) c ->
        is_derivable_wf C (l ∪ {[ <{ b /\ d }> ]}) c
    | wrl_andL2 C l b c d :
        has_type C b ty_prp ->
        is_derivable_wf C (l ∪ {[d]}) c ->
        is_derivable_wf C (l ∪ {[ <{ b /\ d }> ]}) c
    | wrl_andR C l b c :
        is_derivable_wf C l b ->
        is_derivable_wf C l c ->
        is_derivable_wf C l <{ b /\ c }>
    | wrl_impL C l b c d :
        is_derivable_wf C l b ->
        is_derivable_wf C (l ∪ {[d]}) c ->
        is_derivable_wf C (l ∪ {[ <{ b > d }> ]}) c
    | wrl_impR C l b c :
        is_derivable_wf C (l ∪ {[b]}) c ->
        is_derivable_wf C l <{ b > c }>
    | wrl_forL C T l b c t :
        has_type C t T ->
        is_derivable_wf C (l ∪ {[ subst_last C C t b ]}) c ->
        is_derivable_wf C (l ∪ {[ <{for T, b}> ]}) c
    | wrl_forR C T l b sb :
        (forall t, t ∈ sb <-> in_supp b t) ->
        is_derivable_wf (C +: foldr ty_arr T (type_check_other <$> sb)) (sq_set_map (lift C) l) (
          subst_last C (S C) (foldl tm_app (tm_lvl C) sb) b
        ) ->
        is_derivable_wf C l <{for T, b}>
    | wrl_exL C T l b c sb :
        (forall t, t ∈ sb <-> in_supp b t) ->
        is_derivable_wf (C +: foldr ty_arr T (type_check_other <$> sb)) (
          sq_set_map (lift C) l ∪
          {[subst_last C (S C) (foldl tm_app (tm_lvl C) sb) b]}
        ) (lift C c) ->
        is_derivable_wf C (l ∪ {[ <{ex T, b}> ]}) c
    | wrl_exR C T l b t :
        has_type C t T ->
        is_derivable_wf C l (subst_last C C t b) ->
        is_derivable_wf C l <{ex T, b}>
    | wrl_nabL {T b} n (_ : ~ in_supp b (gtm_nom T n)) C l c :
        is_derivable_wf C (l ∪ {[ subst_last C C (gtm_nom T n) b ]}) c ->
        is_derivable_wf C (l ∪ {[ <{nab T, b}> ]}) c
    | wrl_nabR {T b} n (_ : ~ in_supp b (gtm_nom T n)) C l :
        is_derivable_wf C l (subst_last C C (gtm_nom T n) b) ->
        is_derivable_wf C l (<{nab T, b}>)
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
  Theorem is_derivable_wf_wf C l c : is_derivable_wf C l c -> wf_sequent C l c.
  Proof.
    intros D. unfold wf_sequent. induction D; simpl in *.
    - set_unfold. intuition. apply H0. now apply H.
    - split; try assumption.
      intros. set_unfold. congruence.
    - set_unfold. intuition.
    - set_unfold. intuition.
    - set_unfold. intuition.
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
    - unfold wf_sq_set. intuition; [|econstructor].
      + eapply has_type_lift2.
        apply H0. apply sq_set_map_spec. eauto.
      + now apply ht_other2.
      + tm_simpl. eexists; intuition.
        eapply has_type_fold2; try eassumption. apply H.
    - set_unfold. intuition.
      + eapply has_type_lift2. apply H0. left.
        apply sq_set_map_spec. eauto.
      + subst. econstructor; [now apply ht_other2|].
        tm_simpl. eexists; try reflexivity.
        eapply has_type_fold2; auto. apply H.
      + eapply has_type_lift2; eassumption.
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


  Inductive is_derivable : context -> sq_set -> tm -> Prop :=
    | rl_set C l m c :
        l ≡ m ->
        is_derivable C l c ->
        is_derivable C m c
    | rl_id (C : context) l a b :
        tm_equiv C a b ->
        is_derivable C (l ∪ {[a]}) b
    | rl_cut C l m b c :
        has_type C b ty_prp ->
        is_derivable C l b ->
        is_derivable C (m ∪ {[b]}) c ->
        is_derivable C (l ∪ m) c
    | rl_cL C l b c :
        is_derivable C (l ∪ {[b; b]}) c ->
        is_derivable C (l ∪ {[b]}) c
    | rl_botL C l c :
        is_derivable C (l ∪ {[gtm_bot]}) c
    | rl_topR C l :
        is_derivable C l gtm_top
    | rl_orL C l b c d :
        is_derivable C (l ∪ {[b]}) c ->
        is_derivable C (l ∪ {[d]}) c ->
        is_derivable C (l ∪ {[ <{ b \/ d }> ]}) c
    | rl_orR1 C l b c :
        is_derivable C l b ->
        is_derivable C l <{ b \/ c }>
    | rl_orR2 C l b c :
        is_derivable C l c ->
        is_derivable C l <{ b \/ c }>
    | rl_andL1 C l b c d :
        is_derivable C (l ∪ {[b]}) c ->
        is_derivable C (l ∪ {[ <{ b /\ d }> ]}) c
    | rl_andL2 C l b c d :
        is_derivable C (l ∪ {[d]}) c ->
        is_derivable C (l ∪ {[ <{ b /\ d }> ]}) c
    | rl_andR C l b c :
        is_derivable C l b ->
        is_derivable C l c ->
        is_derivable C l <{ b /\ c }>
    | rl_impL C l b c d :
        is_derivable C l b ->
        is_derivable C (l ∪ {[d]}) c ->
        is_derivable C (l ∪ {[ <{ b > d }> ]}) c
    | rl_impR C l b c :
        is_derivable C (l ∪ {[b]}) c ->
        is_derivable C l <{ b > c }>
    | rl_forL C T l b c t :
        has_type C t T ->
        is_derivable C (l ∪ {[ subst_last C C t b ]}) c ->
        is_derivable C (l ∪ {[ <{for T, b}> ]}) c
    | rl_forR C T l b sb :
        (forall t, t ∈ sb <-> in_supp b t) ->
        is_derivable (C +: foldr ty_arr T (type_check_other <$> sb)) (sq_set_map (lift C) l) (
          subst_last C (S C) (foldl tm_app (tm_lvl C) sb) b
        ) ->
        is_derivable C l <{for T, b}>
    | rl_exL C T l b c sb :
        (forall t, t ∈ sb <-> in_supp b t) ->
        is_derivable (C +: foldr ty_arr T (type_check_other <$> sb)) (
          sq_set_map (lift C) l ∪
          {[subst_last C (S C) (foldl tm_app (tm_lvl C) sb) b]}
        ) (lift C c) ->
        is_derivable C (l ∪ {[ <{ex T, b}> ]}) c
    | rl_exR C T l b t :
        has_type C t T ->
        is_derivable C l (subst_last C C t b) ->
        is_derivable C l <{ex T, b}>
    | rl_nabL {T b} n (_ : ~ in_supp b (gtm_nom T n)) C l c :
        is_derivable C (l ∪ {[ subst_last C C (gtm_nom T n) b ]}) c ->
        is_derivable C (l ∪ {[ <{nab T, b}> ]}) c
    | rl_nabR {T b} n (_ : ~ in_supp b (gtm_nom T n)) C l :
        is_derivable C l (subst_last C C (gtm_nom T n) b) ->
        is_derivable C l (<{nab T, b}>)
  .

  Notation "[{ sig ; l --> B }]" := (is_derivable sig l B)
    (sig custom stlc_ty, l custom stlc_tm, B custom stlc_tm) : stlc_scope.

  Notation "∅" := empty (in custom stlc_ty) : stlc_scope.
  Notation "∅" := empty (in custom stlc_tm) : stlc_scope.
  Notation "s +: x" := (s ∪ {[x]}) (in custom stlc_tm at level 50, left associativity) : stlc_scope.
  Notation "∅" := empty : stdpp_scope.
  Notation "{[ x ]}" := (singleton x) (in custom stlc_tm) : stlc_scope.

  Theorem union_empty (X : sq_set) : ∅ ∪ X ≡ X.
  Proof. set_unfold. intuition. Qed.

  Instance is_derivable_Proper : Proper ((=) ==> (≡) ==> (=) ==> iff) is_derivable.
  Proof.
    intros ? ** ? ** ? **. subst.
    split; intros H; eapply rl_set; try apply H; easy.
  Qed.


  Theorem is_derivable_wf_is_derivable C l c :
    is_derivable_wf C l c -> [{ C; l --> c }].
  Proof.
    intros DW. induction DW; subst.
    - eapply rl_set; eassumption.
    - rewrite <- union_empty. now apply rl_id.
    - eapply rl_cut; try eassumption.
      apply is_derivable_wf_wf in DW1. destruct DW1. assumption.
    - now apply rl_cL.
  Abort.

  Theorem is_derivable_is_derivable_wf C l c :
    wf_sequent C l c ->  [{ C; l --> c }] -> is_derivable_wf C l c.
  Proof.
    intros W D. induction D.
    - eapply wrl_set; [eassumption|].
  Abort.


  Theorem nom_in_supp b T : exists a, ~ in_supp b (gtm_nom T a).
  Proof. eexists. apply nom_fresh_in_supp. Qed.

  Theorem rl_nabL2 C T b l c :
    exists2 n, ~ in_supp b (gtm_nom T n) &
    (is_derivable C (l ∪ {[ subst_last C C (gtm_nom T n) b ]}) c ->
    is_derivable C (l ∪ {[ <{nab T, b}> ]}) c).
  Proof.
    exists (nom_fresh b).
    - apply nom_fresh_in_supp.
    - intros. eapply rl_nabL.
      + apply nom_fresh_in_supp.
      + eassumption.
  Qed.

  Ltac rl_nabL n := edestruct rl_nabL2 as [n ?X ?H]; apply H; clear H.

  Theorem sq_set_swap (l : sq_set) a b :
    <{ l +: a +: b }> ≡ <{ l +: b +: a }>.
  Proof. set_unfold. intuition. Qed.

  Theorem contrapositive C l b c :
    [{ C ; l +: b --> c }] -> [{ C ; l +: ~ c --> ~ b }].
  Proof.
    intros H.
    apply rl_impR. rewrite sq_set_swap.
    apply rl_impL; try assumption.
    apply rl_botL.
  Qed.

  Theorem in_supp_not B n :
    in_supp <{ ~ B }> n <-> in_supp B n.
  Proof. unfold in_supp. simpl. intuition. Qed.

  Hint Rewrite in_supp_not : tm.

  Theorem rl_id2 C l t :
    is_derivable C (l ∪ {[t]}) t.
  Proof. intros. apply rl_id; easy. Qed.

  (*
  Notation "({ C ; l --> c })" := (wf_sequent C l c -> is_derivable C l c)
    (C custom stlc_ty, l custom stlc_tm, c custom stlc_tm) : stlc_scope.
    *)

  Theorem example1 C l T B :
    [{ C ; l --> (∇ T, ~ B) ≡ ~ (∇ T, B) }].
  Proof.
    destruct (nom_in_supp B T) as [a Ha].
    constructor; constructor.
    - apply (rl_nabL a); tm_simpl; [easy|].
      apply contrapositive. apply (rl_nabL a Ha).
      apply rl_id2.
    - apply (rl_nabR a); tm_simpl; [easy|].
      apply contrapositive. apply (rl_nabR a Ha).
      apply rl_id2.
  Qed.

  Theorem example2 C l T b c :
    [{ C; l --> (∇ T, b \/ c) ≡ (∇ T, b) \/ (∇ T, c) }].
  Proof.
    destruct (nom_in_supp <{ b \/ c }> T) as [n Hn].
    constructor; constructor.
    - apply (rl_nabL n); [easy|].
      tm_simpl. apply rl_orL.
      + apply rl_orR1. apply (rl_nabR n).
        * unfold in_supp in *. simpl in *. intuition.
        * apply rl_id2.
      + apply rl_orR2. apply (rl_nabR n).
        * unfold in_supp in *. simpl in *. intuition.
        * apply rl_id2.
    - apply (rl_nabR n); [easy|].
      tm_simpl. apply rl_orL.
      + apply rl_orR1. apply (rl_nabL n).
        * unfold in_supp in *. simpl in *. intuition.
        * apply rl_id2.
      + apply rl_orR2. apply (rl_nabL n).
        * unfold in_supp in *. simpl in *. intuition.
        * apply rl_id2.
  Qed.
End GLogic.
