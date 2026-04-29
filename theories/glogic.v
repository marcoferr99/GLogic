Require Export g_stlc.
Require sets.
From stdpp Require Import listset.
Export GStlcTheories.
Import sets.


(*************************)
(** * G Logic Deductions *)
(*************************)

Module Type TM_SET.
  Parameter tm_set : Set.
  Declare Instance tm_set_elem_of : ElemOf tm tm_set.
  Declare Instance tm_set_empty : Empty tm_set.
  Declare Instance tm_set_singleton : Singleton tm tm_set.
  Declare Instance tm_set_union : Union tm_set.
  Declare Instance tm_set_semi_set : SemiSet _ tm_set.
  Parameter tm_set_map : (tm -> tm) -> tm_set -> tm_set.
  Axiom tm_set_map_spec :
    forall f s t, t ∈ tm_set_map f s <-> exists a, a ∈ s /\ t = f a.
End TM_SET.

Module tm_set : TM_SET.
  Definition tm_set := listset tm.
  Instance tm_set_elem_of : ElemOf tm tm_set := listset_elem_of.
  Instance tm_set_empty : Empty tm_set := listset_empty.
  Instance tm_set_singleton : Singleton tm tm_set := listset_singleton.
  Instance tm_set_union : Union tm_set := listset_union.
  Instance tm_set_semi_set : SemiSet _ tm_set := listset_simple_set.
  Definition tm_set_map : (tm -> tm) -> tm_set -> tm_set := listset_fmap _ _.

  Theorem tm_set_map_spec :
    forall f s t, t ∈ tm_set_map f s <-> exists a, a ∈ s /\ t = f a.
  Proof.
    intros. unfold tm_set_map. split.
    - intros. apply elem_of_fmap in H as [x]. exists x. intuition.
    - intros [x]. apply elem_of_fmap. exists x. intuition.
  Qed.
End tm_set.


Module Type CLAUSES.
  Parameter clause_f : list ty -> nat -> option gtm.
  Axiom clause_f_spec : forall C l n B, clause_f l n = Some B ->
    let T := type_check_other (gtm_prd l n) in
    has_type C B (ty_arr T T).
End CLAUSES.


Module GLogic.
  Declare Module Clauses : CLAUSES.
  Export tm_set.
  Export Clauses.


  Notation is_form C t := (has_type C t ty_prp).
  Definition wf_tm_set C (l : tm_set) := forall t, t ∈ l -> is_form C t.

  Definition wf_sequent C (p : tm_set) c := wf_tm_set C p /\ is_form C c.

  Instance wf_sequent_Proper : Proper ((=) ==> (≡) ==> (=) ==> iff) wf_sequent.
  Proof.
    intros C ? <- p q E c ? <-.
    unfold wf_sequent, wf_tm_set. intuition; set_solver.
  Qed.

  (***************)
  (** ** Clauses *)
  (***************)

  Theorem has_type_clause {L n B C T} :
    clause_f L n = Some B ->
    has_type C B T <->
    let X := type_check_other (gtm_prd L n) in
    T = ty_arr X X.
  Proof.
    split; intros.
    - eapply has_type_unique > [eassumption|].
      now apply clause_f_spec.
    - simpl in *. subst. eapply clause_f_spec. eassumption.
  Qed.

  Ltac2 ht_clause h :=
    let c := Control.hyp h in
    match! goal with
    | [ o : clause_f _ _ = Some _ |- _ ] =>
      let oc := Control.hyp o in let a := Fresh.in_goal @H in
        assert ($a := proj1 (has_type_clause $oc) $c); simpl in $a; try (ty_injection $a); []
    end.

  Ltac2 Set ht_list as old := fun () => List.append (old ()) [ht_clause].

  Ltac2 htg_clause () :=
    match! goal with
    | [ o : clause_f _ _ = Some _ |- _ ] =>
        let oc := Control.hyp o in
        refine '(proj2 (has_type_clause $oc) _); try reflexivity
    end.

  Ltac2 Set htg_list as old := fun () => List.append (old ()) [htg_clause].


  (***********************)
  (** ** Deduction rules *)
  (***********************)

  Notation "∅" := empty (in custom stlc_ty) : stlc_scope.
  Notation "∅" := empty (in custom stlc_tm) : stlc_scope.
  Notation "∅" := empty : stdpp_scope.
  Infix "∪" := union (in custom stlc_tm at level 50) : stlc_scope.
  Infix "∪" := union : stdpp_scope.
  Notation "s +; x" := (s ∪ {[x]}) (in custom stlc_tm at level 50, left associativity) : stlc_scope.
  Notation "s +; x" := (s ∪ {[x]}) (at level 50, left associativity) : stlc_scope.
  Notation "{[ x ]}" := (singleton x) (in custom stlc_tm) : stlc_scope.
  Notation "{[ x ]}" := (singleton x) : stdpp_scope.


  Inductive is_derivable_wf : context -> tm_set -> tm -> Prop :=
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
        is_derivable_wf C (m +; b) c ->
        is_derivable_wf C (l ∪ m) c
    | wrl_cL C l b c :
        is_derivable_wf C (l +; b +; b) c ->
        is_derivable_wf C (l +; b) c
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
        is_derivable_wf C (l +; b) c ->
        is_derivable_wf C (l +; d) c ->
        is_derivable_wf C (l +; <{ b \/ d }>) c
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
        is_derivable_wf C (l +; b) c ->
        is_derivable_wf C (l +; <{ b /\ d }>) c
    | wrl_andL2 C l b c d :
        has_type C b ty_prp ->
        is_derivable_wf C (l +; d) c ->
        is_derivable_wf C (l +; <{ b /\ d }>) c
    | wrl_andR C l b c :
        is_derivable_wf C l b ->
        is_derivable_wf C l c ->
        is_derivable_wf C l <{ b /\ c }>
    | wrl_impL C l b c d :
        is_derivable_wf C l b ->
        is_derivable_wf C (l +; d) c ->
        is_derivable_wf C (l +; <{ b > d }>) c
    | wrl_impR C l b c :
        is_derivable_wf C (l +; b) c ->
        is_derivable_wf C l <{ b > c }>
    | wrl_forL C T l b c t :
        has_type C t T ->
        is_derivable_wf C (l +; subst_last C C t b) c ->
        is_derivable_wf C (l +; <{for T, b}>) c
    | wrl_forR C T l b sb :
        (forall t, t ∈ sb <-> in_supp b t) ->
        is_derivable_wf (C +: foldr ty_arr T (type_check_other <$> sb)) (tm_set_map (lift C) l) (
          subst_last C (S C) (foldl tm_app (tm_lvl C) sb) b
        ) ->
        is_derivable_wf C l <{for T, b}>
    | wrl_exL C T l b c sb :
        (forall t, t ∈ sb <-> in_supp b t) ->
        is_derivable_wf (C +: foldr ty_arr T (type_check_other <$> sb)) (
          tm_set_map (lift C) l ∪
          {[subst_last C (S C) (foldl tm_app (tm_lvl C) sb) b]}
        ) (lift C c) ->
        is_derivable_wf C (l +; <{ex T, b}>) c
    | wrl_exR C T l b t :
        has_type C t T ->
        is_derivable_wf C l (subst_last C C t b) ->
        is_derivable_wf C l <{ex T, b}>
    | wrl_nabL {T b} n (_ : ~ in_supp b (gtm_nom T n)) C l c :
        is_derivable_wf C (l +; subst_last C C (gtm_nom T n) b) c ->
        is_derivable_wf C (l +; <{nab T, b}>) c
    | wrl_nabR {T b} n (_ : ~ in_supp b (gtm_nom T n)) C l :
        is_derivable_wf C l (subst_last C C (gtm_nom T n) b) ->
        is_derivable_wf C l (<{nab T, b}>)
    | wrl_defL C l L n B c t :
        let p := gtm_prd L n in
        clause_f L n = Some B ->
        is_derivable_wf C (l +; foldl tm_app <{B p}> t) c ->
        is_derivable_wf C (l +; foldl tm_app p t) c
    | wrl_defR C l L n B t :
        let p := gtm_prd L n in
        clause_f L n = Some B ->
        is_derivable_wf C l (foldl tm_app <{B p}> t) ->
        is_derivable_wf C l (foldl tm_app p t)
  .

  Inductive is_derivable : context -> tm_set -> tm -> Prop :=
    | rl_set C l m c :
        l ≡ m ->
        is_derivable C l c ->
        is_derivable C m c
    | rl_id (C : context) l a b :
        tm_equiv C a b ->
        is_derivable C (l +; a) b
    | rl_cut C l m b c :
        has_type C b ty_prp ->
        is_derivable C l b ->
        is_derivable C (m +; b) c ->
        is_derivable C (l ∪ m) c
    | rl_cL C l b c :
        is_derivable C (l +; b +; b) c ->
        is_derivable C (l +; b) c
    | rl_botL C l c :
        is_derivable C (l +; gtm_bot) c
    | rl_topR C l :
        is_derivable C l gtm_top
    | rl_orL C l b c d :
        is_derivable C (l +; b) c ->
        is_derivable C (l +; d) c ->
        is_derivable C (l +; <{ b \/ d }>) c
    | rl_orR1 C l b c :
        is_derivable C l b ->
        is_derivable C l <{ b \/ c }>
    | rl_orR2 C l b c :
        is_derivable C l c ->
        is_derivable C l <{ b \/ c }>
    | rl_andL1 C l b c d :
        is_derivable C (l +; b) c ->
        is_derivable C (l +; <{ b /\ d }>) c
    | rl_andL2 C l b c d :
        is_derivable C (l +; d) c ->
        is_derivable C (l +; <{ b /\ d }>) c
    | rl_andR C l b c :
        is_derivable C l b ->
        is_derivable C l c ->
        is_derivable C l <{ b /\ c }>
    | rl_impL C l b c d :
        is_derivable C l b ->
        is_derivable C (l +; d) c ->
        is_derivable C (l +; <{ b > d }>) c
    | rl_impR C l b c :
        is_derivable C (l +; b) c ->
        is_derivable C l <{ b > c }>
    | rl_forL C T l b c t :
        has_type C t T ->
        is_derivable C (l +; subst_last C C t b) c ->
        is_derivable C (l +; <{for T, b}>) c
    | rl_forR C T l b sb :
        (forall t, t ∈ sb <-> in_supp b t) ->
        is_derivable (C +: foldr ty_arr T (type_check_other <$> sb)) (tm_set_map (lift C) l) (
          subst_last C (S C) (foldl tm_app (tm_lvl C) sb) b
        ) ->
        is_derivable C l <{for T, b}>
    | rl_exL C T l b c sb :
        (forall t, t ∈ sb <-> in_supp b t) ->
        is_derivable (C +: foldr ty_arr T (type_check_other <$> sb)) (
          tm_set_map (lift C) l ∪
          {[subst_last C (S C) (foldl tm_app (tm_lvl C) sb) b]}
        ) (lift C c) ->
        is_derivable C (l +; <{ex T, b}>) c
    | rl_exR C T l b t :
        has_type C t T ->
        is_derivable C l (subst_last C C t b) ->
        is_derivable C l <{ex T, b}>
    | rl_nabL {T b} n (_ : ~ in_supp b (gtm_nom T n)) C l c :
    is_derivable C (l +; subst_last C C (gtm_nom T n) b) c ->
    is_derivable C (l +; <{nab T, b}>) c
    | rl_nabR {T b} n (_ : ~ in_supp b (gtm_nom T n)) C l :
        is_derivable C l (subst_last C C (gtm_nom T n) b) ->
        is_derivable C l (<{nab T, b}>)
    | rl_defL C l L n B c t :
        let p := gtm_prd L n in
        clause_f L n = Some B ->
        is_derivable C (l +; foldl tm_app <{B p}> t) c ->
        is_derivable C (l +; foldl tm_app p t) c
    | rl_defR C l L n B t :
        let p := gtm_prd L n in
        clause_f L n = Some B ->
        is_derivable C l (foldl tm_app <{B p}> t) ->
        is_derivable C l (foldl tm_app p t)
  .

  Notation "[{ sig ; l --> B }]" := (is_derivable sig l B)
    (sig custom stlc_ty, l custom stlc_tm, B custom stlc_tm) : stlc_scope.


  Instance is_derivable_wf_Proper :
    Proper ((=) ==> (≡) ==> (=) ==> iff) is_derivable_wf.
  Proof.
    intros ? ** ? ** ? **. subst.
    split; intros H; eapply wrl_set; try (apply H); easy.
  Qed.

  Instance is_derivable_Proper :
    Proper ((=) ==> (≡) ==> (=) ==> iff) is_derivable.
  Proof.
    intros ? ** ? ** ? **. subst.
    split; intros H; eapply rl_set; try (apply H); easy.
  Qed.


  (*
  Theorem has_type_fold C T A h l t :
    length h = length l ->
    has_type C t (foldr ty_arr T h) ->
    has_type C (foldl tm_app t l) A ->
    A = T.
  Proof.
    intros L H1 H2.
    apply has_type_fold_app in H2 as [X H2 F].
    apply (has_type_unique _ _ H1) in H2.
    clear l t L H1 F.
  Qed.
  *)

  (*
  Theorem has_type_fold C T h l t :
    has_type C t (foldr ty_arr T h) ->
    Forall2 (fun x X => has_type C x X) l h ->
    has_type C (foldl tm_app t l) T.
  Proof.
    revert h t. induction l; intros h t Ht F.
    - inversion F. now subst.
    - simpl. destruct h; inversion F. subst.
      eapply IHl; try eassumption.
      has_type. now (exists t0).
  Qed.

  Theorem th T l :
    l <> [] -> T <> foldr ty_arr T l.
  Proof.
    intros Hl E. destruct l > [congruence|]. simpl in *.
    clear Hl. revert t l E.
    ty_induction T; intros t l E; try (ty_discriminate E).
    rewrite <- foldr_snoc in E.
    destruct l.
    - simpl in *. ty_injection E.
      clear IHT1 IHT2 E E0.
      ty_induction T2; try (ty_discriminate E1).
      ty_injection E1. auto.
    - simpl in E. ty_injection E.
      eapply IHT2. rewrite <- E1.
      eassumption.
  Qed.

  Theorem th2 C T t l :
    l <> [] ->
    has_type C (foldl tm_app t l) T -> has_type C t T -> False.
  Proof.
    revert t. induction l > [congruence|]; intros t Hl H1 H2.
    simpl in *. eapply IHl.
    2:{ eassumption. }
    2:{ has_type.

  Theorem has_type_fold_2 C T h l t :
    has_type C t (foldr ty_arr T h) ->
    has_type C (foldl tm_app t l) T ->
    Forall2 (fun x X => has_type C x X) l h.
  Proof.
    revert t h. induction l; intros t h Ht H.
    - simpl in *.
      apply (has_type_unique _ _ H) in Ht.
      clear H. destruct h > [constructor|].
      apply th in Ht > [easy|].
      congruence.
    - destruct h.
      + simpl in *.
        Search foldl.
        rewrite <- foldl_snoc in H.
        has_type.
      simpl in *. clear IHh. exfalso.
      ty_induction T; try (ty_discriminate Ht).
      destruct h; simpl in *.
      + ty_injection Ht. auto.
      + simpl in Ht.
        ty_injection Ht.
        apply IHT2.
        assert (forall A B l, foldr ty_arr (ty_arr A B) l = ty_arr (foldr ty_arr A l) B). {
          intros. induction l; simpl in *; try reflexivity.
          rewrite IHl. simpl.
          -
        }
  - (* Case ty_arr T1 T2 *)
    destruct l as [| a l']; [congruence |].
    simpl in Ht. ltac1:(ty_injection Ht).
    (* H1 is the equality for the codomain: T2 = foldr ty_arr (ty_arr T1 T2) l' *)
    rewrite foldr_ty_arr_append in H1.
    eapply (H0 (l' ++ [T1])); [|assumption].
    intros N. ltac1:(apply app_eq_nil in N as [_ N]; discriminate).
  - (* Case ty_other *)
    destruct l; [congruence | simpl in Ht; ltac1:(ty_discriminate Ht)].exfalso.
      revert T Ht.
      induction h; intros T Ht.
      + simpl in Ht.
        ty_induction T; try (ty_discriminate Ht).
        ty_injection Ht. auto.
      + simpl in *.
        ty_induction T; try (ty_discriminate Ht).
        eapply IHh. apply Ht.
      + constructor.
      + simpl in *.
  Admitted.
  *)

  Theorem has_type_fold C T sb b :
    (forall t, t ∈ sb -> in_supp b t) ->
    has_type (C +: foldr ty_arr T (type_check_other <$> sb)) (subst_last C (S C) (foldl tm_app (tm_lvl C) sb) b) -[ o ]- ->
    has_type (C +: T) b ty_prp.
  Proof.
    intros.
    eapply (has_type_subst_last2 _ (C +: foldr ty_arr T (type_check_other <$> sb)));
      simpl; try eassumption; try lia.
    - intros. now rewrite decide_True.
    - apply has_type_fold_app. eexists; has_type.
      + simpl. rewrite decide_False; ltac1:(intuition lia).
      + remember (C +: foldr ty_arr T (type_check_other <$> sb)) as D eqn : ED.
        clear ED H0. induction sb; simpl in *; constructor.
        * constructor. set_unfold. eapply in_supp_other. auto.
        * set_unfold. auto.
  Qed.

  Theorem has_type_fold2 C T sb b :
    (forall t, t ∈ sb -> in_supp b t) ->
    has_type (C +: T) b ty_prp ->
    has_type (C +: foldr ty_arr T (type_check_other <$> sb)) (subst_last C (S C) (foldl tm_app (tm_lvl C) sb) b) -[ o ]-.
  Proof.
    intros.
    eapply has_type_subst_last1.
    - simpl. lia.
    - intros. simpl. now rewrite decide_True.
    - apply has_type_fold_app. eexists; has_type.
      + simpl. rewrite decide_False; ltac1:(intuition lia).
      + remember (C +: foldr ty_arr T (type_check_other <$> sb)) as D eqn : ED.
        clear ED H0. induction sb; simpl in *; constructor.
        * constructor. set_unfold. eapply in_supp_other. auto.
        * set_unfold. auto.
    - assumption.
  Qed.

  Theorem foldr_ty_arr_inj T L M :
    foldr ty_arr T L = foldr ty_arr T M -> L = M.
  Proof.
    revert M.
    induction L; intros M E. simpl in *.
    - destruct (decide (M = [])) > [easy|].
      exfalso. apply (StrictOrder_Irreflexive T).
      rewrite E at 2. now apply ty_sub_foldr.
    - destruct M; simpl in *.
      + rewrite <- foldr_cons in E.
        exfalso. apply (StrictOrder_Irreflexive T).
        rewrite <- E at 2. now apply ty_sub_foldr.
      + ty_injection E. f_equal. now apply IHL.
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
      repeat (eapply ht_app); auto. now apply ht_other2.
    - intuition. repeat (eapply ht_app); try eassumption. now apply ht_other2.
    - intuition. repeat (eapply ht_app); try eassumption. now apply ht_other2.
    - set_unfold. intuition. subst.
      repeat (eapply ht_app); eauto. now apply ht_other2.
    - set_unfold. intuition. subst.
      repeat (eapply ht_app); eauto. now apply ht_other2.
    - intuition. repeat (eapply ht_app); try eassumption. now apply ht_other2.
    - set_unfold. intuition. subst.
      repeat (eapply ht_app); eauto. now apply ht_other2.
    - set_unfold. intuition.
      repeat (eapply ht_app); eauto. now apply ht_other2.
    - set_unfold. intuition. subst. econstructor.
      + now apply ht_other2.
      + has_type. eapply has_type_subst_last2; eauto.
    - unfold wf_tm_set. intuition > [|econstructor].
      + eapply has_type_lift2.
        apply H0. apply tm_set_map_spec. eauto.
      + now apply ht_other2.
      + has_type. eapply has_type_fold; try eassumption. apply H.
    - set_unfold. intuition.
      + eapply has_type_lift2. apply H0. left.
        apply tm_set_map_spec. eauto.
      + subst. econstructor > [now apply ht_other2|].
        has_type. eapply has_type_fold; auto. apply H.
      + eapply has_type_lift2; eassumption.
    - intuition. econstructor > [now apply ht_other2|].
      has_type. eapply has_type_subst_last2; eauto.
    - set_unfold. intuition. subst.
      econstructor > [now apply ht_other2|].
      has_type. eapply has_type_subst_last2; eauto.
      now constructor.
    - intuition. econstructor > [now apply ht_other2|].
      has_type. eapply has_type_subst_last2; eauto.
      now constructor.
    - set_unfold. intuition. subst.
      assert (is_form C (foldl tm_app <{ B p }> t)) by auto.
      has_type.
      exists L > [assumption|].
      ltac1:(replace L with x) > [assumption|].
      eapply foldr_ty_arr_inj. eassumption.
    - set_unfold. intuition.
      has_type. exists L > [assumption|].
      ltac1:(replace L with x) > [assumption|].
      eapply foldr_ty_arr_inj. eassumption.
  Qed.

  Theorem rl_wL C l m c :
    [{ C; m --> c }] -> [{ C; l ∪ m --> c }].
  Proof.
    revert C l m c.
    assert (MU : forall C h l, tm_set_map (lift C) <{ h ∪ l }> ≡ (tm_set_map (lift C) h) ∪ (tm_set_map (lift C) l) ). {
      intros C h1 h2 x. set_unfold. repeat (rewrite tm_set_map_spec).
      set_unfold. split.
      - intros [y [Hy ->]]. destruct Hy; ltac1:(intuition eauto).
      - intros [[y [Hy ->]] | [y [Hy ->]]]; eauto.
    }
    intros * H. revert l.
    induction H; intros h; try (rewrite union_assoc in *).
    - now rewrite <- H.
    - now apply rl_id.
    - eapply rl_cut; eauto.
    - apply rl_cL. specialize IHis_derivable with h.
      now repeat (rewrite union_assoc in *).
    - apply rl_botL.
    - apply rl_topR.
    - apply rl_orL; now rewrite <- union_assoc.
    - now apply rl_orR1.
    - now apply rl_orR2.
    - apply rl_andL1; now rewrite <- union_assoc.
    - apply rl_andL2; now rewrite <- union_assoc.
    - now apply rl_andR.
    - apply rl_impL > [easy|]. now rewrite <- union_assoc.
    - apply rl_impR. now rewrite <- union_assoc.
    - eapply rl_forL > [eassumption|].
      now rewrite <- union_assoc.
    - eapply rl_forR; try eassumption.
      now rewrite MU.
    - eapply rl_exL; try eassumption.
      now rewrite MU, <- union_assoc.
    - eapply rl_exR; eauto.
    - eapply rl_nabL; try eassumption.
      now rewrite <- union_assoc.
    - eapply rl_nabR; eauto.
    - eapply rl_defL > [eassumption|].
      now rewrite <- union_assoc.
    - eapply rl_defR; eauto.
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
    - now apply rl_wL.
    - rewrite <- union_empty. apply rl_botL.
    - apply rl_topR.
    - now apply rl_orL.
    - now apply rl_orR1.
    - now apply rl_orR2.
    - now apply rl_andL1.
    - now apply rl_andL2.
    - now apply rl_andR.
    - now apply rl_impL.
    - now apply rl_impR.
    - eapply rl_forL; eassumption.
    - eapply rl_forR; eassumption.
    - eapply rl_exL; eassumption.
    - eapply rl_exR; eassumption.
    - eapply rl_nabL; eassumption.
    - eapply rl_nabR; eassumption.
    - eapply rl_defL; eassumption.
    - eapply rl_defR; eassumption.
  Qed.

  Theorem is_derivable_is_derivable_wf C l c :
    wf_sequent C l c ->  [{ C; l --> c }] -> is_derivable_wf C l c.
  Proof.
    intros [] D. unfold wf_tm_set in *. induction D; set_unfold.
    - eapply wrl_set > [eassumption|].
      apply IHD; set_solver.
    - apply wrl_wL; try auto.
      apply wrl_id; auto.
    - eapply wrl_cut; first [apply IHD1 | apply IHD2]; set_solver.
    - apply wrl_cL. apply IHD; set_solver.
    - apply wrl_wL > [|apply wrl_botL]; set_solver.
    - assert (E : l ≡ l ∪ ∅) > [set_solver|].
      rewrite E. apply wrl_wL > [|apply wrl_topR].
      clear E. set_solver.
    - assert (is_form C <{b \/ d}>) by auto.
      apply wrl_orL; first [apply IHD1 | apply IHD2];
        intuition; subst; now has_type.
    - apply wrl_orR1.
      + now has_type.
      + apply IHD; intuition. now has_type.
    - apply wrl_orR2.
      + now has_type.
      + apply IHD; intuition. now has_type.
    - assert (is_form C <{b /\ d}>) by auto.
      apply wrl_andL1 > [now has_type|].
      apply IHD; intuition. subst. now has_type.
    - assert (is_form C <{b /\ d}>) by auto.
      apply wrl_andL2 > [now has_type|].
      apply IHD; intuition. subst. now has_type.
    - assert (is_form C <{b /\ c}>) by auto. apply wrl_andR.
      + apply IHD1. intuition. now has_type.
      + apply IHD2. intuition. now has_type.
    - assert (is_form C <{b > d}>) by auto. apply wrl_impL.
      + apply IHD1. intuition. now has_type.
      + apply IHD2; intuition. subst. now has_type.
    - assert (is_form C <{b > c}>) by auto. apply wrl_impR.
      apply IHD; intuition; subst; now has_type.
    - eapply wrl_forL > [eassumption|].
      apply IHD; intuition. subst.
      eapply has_type_subst_last_s1 > [eassumption|].
      assert (is_form C <{for T, b}>) by auto.
      now has_type.
    - eapply wrl_forR > [eassumption|].
      apply IHD; intuition.
      + apply tm_set_map_spec in H2 as [a [Ha1 Ha2]]. subst.
        has_type. auto.
      + apply has_type_fold2 > [apply H1|].
        now has_type.
    - eapply wrl_exL > [eassumption|].
      apply IHD; intuition.
      + apply tm_set_map_spec in H3 as [a [Ha1 Ha2]]. subst.
        has_type. auto.
      + subst. apply has_type_fold2 > [apply H1|].
        assert (is_form C <{ex T, b}>) by auto.
        now has_type.
      + now has_type.
    - eapply wrl_exR > [eassumption|].
      apply IHD; intuition.
      eapply has_type_subst_last_s1 > [eassumption|].
      now has_type.
    - eapply wrl_nabL > [eassumption|].
      apply IHD; intuition. subst.
      eapply has_type_subst_last_s1.
      + now apply ht_other.
      + assert (is_form C <{nab T, b}>) by auto.
        now has_type.
    - eapply wrl_nabR > [eassumption|].
      apply IHD; intuition.
      eapply has_type_subst_last_s1.
      + now apply ht_other.
      + now has_type.
    - eapply wrl_defL > [eassumption|].
      apply IHD; intuition. subst.
      assert (is_form C (foldl tm_app p t)) by auto.
      has_type. exists L.
      + has_type_goal (). eexists > [|eassumption].
        has_type_goal ().
      + ltac1:(replace L with x) > [assumption|].
        eapply foldr_ty_arr_inj. eassumption.
    - eapply wrl_defR > [eassumption|].
      apply IHD; intuition.
      has_type. exists L.
      + has_type_goal (). eexists > [|eassumption].
        has_type_goal ().
      + ltac1:(replace L with x) > [assumption|].
        eapply foldr_ty_arr_inj. eassumption.
  Qed.


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

  (*
  Ltac rl_nabL n := edestruct rl_nabL2 as [n ?X ?H]; apply H; clear H.
  *)

  Theorem tm_set_swap (l : tm_set) a b :
    <{ l +; a +; b }> ≡ <{ l +; b +; a }>.
  Proof. set_unfold. intuition. Qed.

  Theorem contrapositive C l b c :
    [{ C ; l +; b --> c }] -> [{ C ; l +; ~ c --> ~ b }].
  Proof.
    intros H.
    apply rl_impR. rewrite tm_set_swap.
    apply rl_impL; try assumption.
    apply rl_botL.
  Qed.

  Hint Rewrite in_supp_not : tm.

  Theorem rl_id2 C l t : is_derivable C (l ∪ {[t]}) t.
  Proof. intros. apply rl_id; easy. Qed.

  (*
  Notation "({ C ; l --> c })" := (wf_sequent C l c -> is_derivable C l c)
    (C custom stlc_ty, l custom stlc_tm, c custom stlc_tm) : stlc_scope.
    *)
End GLogic.
