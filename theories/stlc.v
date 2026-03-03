Require Export stlc_types.


(***********************************)
(** * Simply Typed Lambda Calculus *)
(***********************************)


(*****************)
(** ** Interface *)
(*****************)

Declare Custom Entry stlc_tm.

Module Type STLC.
  Declare Module Ty : TY.
  Declare Module Rlist : RLIST.
  Module TyTheories := TyTheories Ty Rlist.
  Export TyTheories.

  (** *** Terms *)

  Parameter tm : Set.
  Parameter tm_lvl : nat -> tm.
  Parameter tm_app : tm -> tm -> tm.
  Parameter tm_abs : ty -> tm -> tm.

  Parameter tm_other : tm -> Prop.
  Axiom tm_other_lvl : forall n, ~ tm_other (tm_lvl n).

  Parameter tm_rect :
    forall P : tm -> Type,
    (forall n, P (tm_lvl n)) ->
    (forall s, P s -> forall t, P t -> P (tm_app s t)) ->
    (forall T t, P t -> P (tm_abs T t)) ->
    (forall t, tm_other t -> P t) ->
    forall t, P t.

  Axiom tm_rect_lvl : forall P l a b o n, tm_rect P l a b o (tm_lvl n) = l n.
  Axiom tm_rect_app : forall P l a b o s t,
    tm_rect P l a b o (tm_app s t) = a _ (tm_rect P l a b o s) _ (tm_rect P l a b o t).
  Axiom tm_rect_abs : forall P l a b o T t,
    tm_rect P l a b o (tm_abs T t) = b T _ (tm_rect P l a b o t).
  Axiom tm_rect_other : forall t P l a b o,
    forall O : tm_other t, tm_rect P l a b o t = o t O.

  (** *** Typing Relation *)

  Parameter has_type : context -> tm -> ty -> Prop.

  Axiom has_type_lvl : forall c n T,
    has_type c (tm_lvl n) T <-> c !! n = Some T.

  Axiom has_type_app : forall c s t B,
    has_type c (tm_app s t) B <->
    exists A, has_type c s (ty_arr A B) /\  has_type c t A.

  Axiom has_type_abs : forall c A T t,
    has_type c (tm_abs A t) T <->
    exists B, has_type (c +: A) t B /\ T = -[ A -> B ]-.

  Axiom has_type_other_indep : forall c d t T,
    tm_other t -> has_type c t T -> has_type d t T.

  Axiom has_type_other_unique : forall c t A B,
    tm_other t -> has_type c t A -> has_type c t B -> A = B.
End STLC.


(****************)
(** ** Theories *)
(****************)

Module StlcTheories (Stlc : STLC).
  Export Stlc.


  (** *** Terms *)

  (** Notations *)
  Coercion tm_lvl : nat >-> tm.

  (** Tactics *)
  Create HintDb tm.
  Hint Rewrite tm_rect_lvl tm_rect_app tm_rect_abs : tm.
  Hint Rewrite tm_rect_other using assumption : tm.
  Hint Rewrite has_type_lvl has_type_app has_type_abs : tm.
  Ltac tm_simpl := repeat (simpl in *; autorewrite with tm in *).
  Ltac tm_simpl1 H := repeat (simpl in H; autorewrite with tm in H).
  Ltac tm_simplg := repeat (simpl; autorewrite with tm).


  Definition tm_rec (P : tm -> Set) := tm_rect P.
  Definition tm_ind (P : tm -> Prop) := tm_rect P.

  Inductive tmv : Set :=
    | tmv_lvl : nat -> tmv
    | tmv_app : tmv -> tmv -> tmv
    | tmv_abs : ty -> tmv -> tmv
    | tmv_other : tm -> tmv.

  Definition to_tmv : tm -> tmv :=
    tm_rec _
      (fun n => tmv_lvl n)
      (fun s fs t ft => tmv_app fs ft)
      (fun T t ft => tmv_abs T ft)
      (fun t _ => tmv_other t).

  Theorem to_tmv_lvl n : to_tmv (tm_lvl n) = tmv_lvl n.
  Proof. unfold to_tmv. now tm_simpl. Qed.

  Theorem to_tmv_app s t : to_tmv (tm_app s t) = tmv_app (to_tmv s) (to_tmv t).
  Proof. unfold to_tmv. now tm_simpl. Qed.

  Theorem to_tmv_abs T t : to_tmv (tm_abs T t) = tmv_abs T (to_tmv t).
  Proof. unfold to_tmv. now tm_simpl. Qed.

  Theorem to_tmv_other t : tm_other t -> to_tmv t = tmv_other t.
  Proof. intros. unfold to_tmv. now tm_simpl. Qed.

  Hint Rewrite to_tmv_lvl to_tmv_app to_tmv_abs : tm.
  Hint Rewrite to_tmv_other using assumption : tm.

  Fixpoint to_tm t : tm :=
    match t with
    | tmv_lvl n => tm_lvl n
    | tmv_app a b => tm_app (to_tm a) (to_tm b)
    | tmv_abs T t => tm_abs T (to_tm t)
    | tmv_other t => t
    end.

  Theorem to_tm_to_tmv t : to_tm (to_tmv t) = t.
  Proof.
    induction t using tm_ind; unfold to_tmv in *; tm_simpl;
      unfold to_tmv; congruence.
  Qed.

  Hint Rewrite to_tm_to_tmv : tm.


  Ltac tmv_f_equal H := apply (f_equal to_tmv) in H; tm_simpl1 H.
  Ltac tm_discriminate1 H := tmv_f_equal H; discriminate H.
  Ltac tm_discriminate :=
    match goal with | [H : _ |- _] => tm_discriminate1 H end.
  Ltac tm_injection H := tmv_f_equal H; injection H.


  (** *** Typing *)

  Theorem has_type_unique c t A B :
    has_type c t A -> has_type c t B -> A = B.
  Proof.
    generalize dependent B. generalize dependent A.
    generalize dependent c.
    induction t using tm_ind; intros c A B HA HB; tm_simpl.
    - congruence.
    - destruct HA as (X & HXt1 & HXt2).
      destruct HB as (Y & HYt1 & HYt2).
      eapply IHt1 in HXt1; [|eassumption].
      apply ty_arr_inj in HXt1 as [_ H]. now symmetry.
    - destruct HA as (X & HXt1 & HXt2).
      destruct HB as (Y & HYt1 & HYt2).
      rewrite HXt2, HYt2. f_equal. eapply IHt; eassumption.
    - eapply has_type_other_unique; eassumption.
  Qed.

  (** Apply "f" to all variables in the term "t" *)
  Definition level_map (f : nat -> nat) (t : tm) : tm :=
    (fix fx f x :=
    match x with
    | tmv_lvl n => tm_lvl (f n)
    | tmv_app a b => tm_app (fx f a) (fx f b)
    | tmv_abs T t => tm_abs T (fx f t)
    | tmv_other t => t
    end) f (to_tmv t).

  Theorem level_map_f_eq f g t :
    (forall n, f n = g n) -> level_map f t = level_map g t.
  Proof.
    intros H. unfold level_map. simpl.
    induction t using tm_ind; repeat tm_simpl; congruence.
  Qed.

  Definition free_level_map f m :=
    level_map (fun n => if decide (n < m) then f n else n).

  Theorem has_type_free_level_map f c d t T :
    |(c)| = |(d)| -> (forall n, d !! f n = c !! n) ->
    has_type c t T ->
    has_type d (free_level_map f |(c)| t) T.
  Proof.
    generalize dependent T.
    generalize dependent d. generalize dependent c.
    generalize dependent f.
    induction t as [| | t |] using tm_ind; intros f c d T L Hf HT;
      unfold free_level_map, level_map; tm_simpl.
    - destruct (decide (n < |(c)|)) as [Hn | Hn].
      + now rewrite Hf.
      + exfalso. apply Hn. apply is_Some_lookup.
        econstructor. eassumption.
    - destruct HT as [A [Ht1 Ht2]].
      exists A. split; eauto.
    - destruct HT as [B [Hb Ht]].
      exists B. split; [|assumption].
      generalize level_map_f_eq. intros E.
      unfold level_map in E. erewrite E; clear E.
      + apply (IHt (fun n => if decide (n < |(c)|) then f n else n));
          try eassumption; [repeat rewrite rlength_rcons; congruence|].
        intros n.
        lookup_rcons_spec c t n Hn En; destruct (decide (n < |(c)|)); try lia.
        * rewrite lookup_rcons_lt; try auto.
          apply is_Some_lookup in l. destruct l.
          eapply is_Some_lookup. econstructor.
          rewrite Hf. eassumption.
        * subst. rewrite lookup_rcons_eq; auto.
        * rewrite lookup_None1; try reflexivity; rewrite rlength_rcons; lia.
      + intros n. simpl.
        destruct (decide (n < |(c)|)), (decide (n < |(c +: t)|));
          try reflexivity.
        rewrite rlength_rcons in *. lia.
    - eapply has_type_other_indep; eassumption.
  Qed.


  (** Apply "f" to all bound variables in the term "t" *)
  Definition bound_level_map f m :=
    level_map (fun n => if decide (m <= n) then f n else n).

  Theorem has_type_bound_level_map_h l m c d t T :
    (l <= |(c)|) ->
    (|(d)| = m + |(c)|) ->
    (forall n, n >= l -> d !! (m + n) = c !! n) ->
    (forall n, n < l -> d !! n = c !! n) ->
    has_type c t T <->
    has_type d (bound_level_map (add m) l t) T.
  Proof.
    generalize dependent T.
    generalize dependent d. generalize dependent c.
    induction t as [| | t |] using tm_ind;
    intros c d T Hl L Hlg Hll; unfold bound_level_map, level_map in *; tm_simpl.
    - destruct (decide (l <= n)).
      + now rewrite Hlg.
      + rewrite Hll; [easy|lia].
    - split; intros (A & H1 & H2); exists A; split;
        first [eapply IHt1 | eapply IHt2]; eauto.
    - split; intros (B & Hc & HB); exists B; split; try assumption.
      + apply (IHt (c +: t)); try assumption; try intros n Hn.
        * rewrite rlength_rcons. lia.
        * repeat rewrite rlength_rcons. lia.
        * lookup_rcons_spec c t n Ic Ec; lookup_rcons_spec d t (m + n) Id Ed;
          try lia; auto.
        * lookup_rcons_spec c t n Ic Ec; lookup_rcons_spec d t n Id Ed;
            try lia; auto.
      + eapply (IHt (c +: t)); try eassumption; try intros n Hn.
        * rewrite rlength_rcons. lia.
        * repeat rewrite rlength_rcons. lia.
        * lookup_rcons_spec c t n Ic Ec; lookup_rcons_spec d t (m + n) Id Ed;
            try lia; auto.
        * lookup_rcons_spec c t n Ic Ec; lookup_rcons_spec d t n Id Ed;
            try lia; auto.
    - split; eapply has_type_other_indep; eassumption.
  Qed.

  Theorem has_type_bound_level_map1 m c d t T :
    (|(d)| = m + |(c)|) ->
    (forall n, n < |(c)| -> d !! n = c !! n) ->
    has_type c t T ->
    has_type d (bound_level_map (add m) |(c)| t) T.
  Proof.
    intros. rewrite <- has_type_bound_level_map_h; try eassumption; [lia|].
    intros n Hn. repeat rewrite lookup_None1; auto. lia.
  Qed.

  Theorem has_type_bound_level_map_S C c t T :
    has_type C t T ->
    has_type (C +: c) (bound_level_map S |(C)| t) T.
  Proof.
    intros Ht. unfold bound_level_map. erewrite level_map_f_eq.
    - apply (has_type_bound_level_map1 1); try eassumption.
      + rewrite rlength_rcons. lia.
      + intros. rewrite lookup_rcons_lt; easy.
    - intros. reflexivity.
  Qed.

  Theorem has_type_bound_level_map2 m c d t T :
    (|(d)| = m + |(c)|) ->
    (forall n, n < |(c)| -> d !! n = c !! n) ->
    has_type d (bound_level_map (add m) |(c)| t) T ->
    has_type c t T.
  Proof.
    intros. eapply has_type_bound_level_map_h; try eassumption; [lia|].
    intros n Hn. repeat rewrite lookup_None1; auto. lia.
  Qed.


  (********************)
  (** ** Substitution *)
  (********************)

  Definition subst m l t :=
    (fix fx m l t :=
    match t with
    | tmv_lvl n => lookup_default (tm_lvl n) n l
    | tmv_app a b => tm_app (fx m l a) (fx m l b)
    | tmv_abs T t => tm_abs T (fx (S m) ((bound_level_map S m <$> l) +: tm_lvl m) t)
    | tmv_other t => t
    end) m l (to_tmv t).

  Theorem has_type_subst_h n Rn (r : rlist tm) (R C : context) (c : ty) :
    |(r)| = |(R)| ->
    (forall rn, r !! n = Some rn -> R !! n = Some Rn -> has_type C rn Rn) ->
    (forall rn, ((bound_level_map S |( C )| <$> r) +: tm_lvl |( C )|) !! n = Some rn -> (R +: c) !! n = Some Rn -> has_type (C +: c) rn Rn).
  Proof.
    intros L F **.
    destruct (lt_total n |(r)|) as [Ln | [En | Gn]].
    - rewrite lookup_rcons_lt in H; [|now rewrite rlength_fmap].
      rewrite lookup_fmap in H.
      apply fmap_Some in H as (x & Hx1 & Hx2).
      subst rn. apply has_type_bound_level_map_S.
      eapply F; [eassumption|].
      rewrite lookup_rcons_lt in H0; [assumption|].
      now rewrite <- L.
    - rewrite lookup_rcons_eq in H; [|now rewrite rlength_fmap].
      injection H. intros. subst. tm_simpl.
      rewrite <- H0.
      repeat rewrite @lookup_rcons_eq; auto.
    - rewrite lookup_rcons_gt in H; [discriminate|now rewrite rlength_fmap].
  Qed.

  Theorem has_type_subst1 C T R t r :
    |(r)| = |(R)| ->
    (forall n rn Rn, r !! n = Some rn -> R !! n = Some Rn -> has_type C rn Rn) ->
    has_type R t T ->
    has_type C (subst |(C)| r t) T.
  Proof.
    generalize dependent r. generalize dependent R.
    generalize dependent T. generalize dependent C.
    induction t as [| |c ? IH| ] using tm_ind;
      simpl; intros C T R r L F HT;
      unfold subst in *; tm_simpl.
    - unfold lookup_default.
      destruct (r !! n) eqn : E; [now apply (F n) |].
      apply lookup_None2 in E.
      rewrite @lookup_None1 in HT; [discriminate|].
      now rewrite <- L.
    - destruct HT as (A & Ht1 & Ht2). exists A. split; eauto.
    - destruct HT as (B & H & HB). exists B. split; [|assumption].
      replace (S |(C)|) with (|(C +: c)|); [|apply rlength_rcons].
      eapply IH; try eassumption.
      + repeat rewrite rlength_rcons. rewrite rlength_fmap.
        now f_equal.
      + intros. eapply has_type_subst_h; eauto.
    - eapply has_type_other_indep; eassumption.
  Qed.

  Theorem has_type_subst2 C T R t r :
    |(C)| <= |(R)| -> |(r)| = |(R)| ->
    (forall n rn Rn, r !! n = Some rn -> R !! n = Some Rn -> has_type C rn Rn) ->
    has_type C (subst |(C)| r t) T ->
    has_type R t T.
  Proof.
    generalize dependent r. generalize dependent R.
    generalize dependent T. generalize dependent C.
    induction t as [| | t |] using tm_ind;
    simpl; intros C T R r L E F HT.
    - assert (HT1 := HT). unfold subst in HT; tm_simpl1 HT.
      assert (exists A, has_type R n A). {
        destruct (decide (n < |(R)|)) as [Hn | Hn].
        - apply is_Some_lookup in Hn as [x Hx].
          exists x. now tm_simpl.
        - unfold lookup_default in HT.
          rewrite lookup_None1 in HT; [|lia].
          tm_simpl.
          rewrite @lookup_None1 in HT; [discriminate|lia].
      }
      destruct H as [X H]. replace T with X; [assumption|].
      eapply has_type_subst1 in H; try eassumption.
      simpl in H. eapply has_type_unique; eassumption.
    - unfold subst in *. tm_simpl.
      destruct HT as (A & Ht1 & Ht2).
      exists A. split; eauto.
    - unfold subst in *. tm_simpl.
      destruct HT as (B & H & HB).
      exists B. split; [|assumption].
      eapply (IHt (C +: t)).
      4:{
        replace (S |(C)|) with (|(C +: t)|) in H; [|rewrite rlength_rcons; lia].
        apply H.
      }
      + repeat rewrite rlength_rcons. lia.
      + repeat rewrite rlength_rcons. f_equal.
        now rewrite rlength_fmap.
      + intros. eapply has_type_subst_h; eauto.
    - unfold subst in HT; tm_simpl.
      eapply has_type_other_indep; eassumption.
  Qed.


  Definition subst_last m s := subst m (build_rlist m tm_lvl +: s).

  Theorem has_type_subst_last C T X s t :
    has_type (C +: T) t X -> has_type C s T ->
    has_type C (subst_last |(C)| s t) X.
  Proof.
    intros Ht Hs.
    eapply has_type_subst1; try eassumption.
    - repeat rewrite rlength_rcons. f_equal.
      apply rlength_build_rlist.
    - intros.
      destruct (lt_total n |(C)|) as [Ln | [En | Gn]].
      + rewrite @lookup_rcons_lt in H, H0; try assumption.
        * rewrite lookup_build_rlist in H; [|assumption].
          injection H. intros <-. now tm_simpl.
        * now rewrite rlength_build_rlist.
      + rewrite @lookup_rcons_eq in H, H0; try assumption.
        * injection H. injection H0. intros <- <-. assumption.
        * now rewrite rlength_build_rlist.
      + rewrite lookup_rcons_gt in H0; [discriminate|lia].
  Qed.

  Definition level_prop P t : bool :=
    (fix fx P t :=
    match t with
    | tmv_lvl m => P m
    | tmv_abs T s => fx P s
    | tmv_app s1 s2 => orb (fx P s1) (fx P s2)
    | _ => false
    end) P (to_tmv t).

  Definition contains_bound_levels m n :=
    level_prop (fun x => andb (leb m x) (ltb x (n + m))).

  Theorem bound_level_map_id m n t :
    contains_bound_levels m n t = false ->
    bound_level_map (add n) m (bound_level_map (fun x => x - n) m t) = t.
  Proof.
    unfold bound_level_map, contains_bound_levels, level_map, level_prop.
    intros L. induction t using tm_ind; tm_simpl; unfold tm_rec in *.
    - f_equal.
      destruct (decide (m <= n0)), (leb_spec m n0), (ltb_spec n0 (n + m));
        try discriminate; try lia.
      + destruct (decide (m <= n0 - n)); lia.
      + destruct (decide (m <= n0)); lia.
    - apply orb_false_elim in L. unfold tm_rec in *.
      intuition congruence.
    - intuition congruence.
    - rewrite (to_tmv_other t0); [|assumption]. now tm_simpl.
  Qed.

  Definition beta_reduction m (t : tm) : tm :=
    (fix fx m t :=
    match t with
    | tmv_lvl n => tm_lvl n
    | tmv_app (tmv_abs T t) s =>
        subst_last m (fx m s) (fx (S m) t)
    | tmv_app s t => tm_app (fx m s) (fx m t)
    | tmv_abs T t => tm_abs T (fx (S m) t)
    | tmv_other t => t
    end) m (to_tmv t).

  Theorem beta_reduction_app_abs m T t s :
    beta_reduction m (tm_app (tm_abs T t) s) = subst_last m (beta_reduction m s) (beta_reduction (S m) t).
  Proof. unfold beta_reduction; now tm_simpl. Qed.

  Theorem beta_reduction_app m s t :
    (forall A a, s <> tm_abs A a) ->
    beta_reduction m (tm_app s t) = tm_app (beta_reduction m s) (beta_reduction m t).
  Proof.
    intros N.
    destruct s using tm_ind; unfold beta_reduction; tm_simpl; try reflexivity.
    exfalso. now eapply N.
  Qed.

  Theorem beta_reduction_abs m T t :
    beta_reduction m (tm_abs T t) = tm_abs T (beta_reduction (S m) t).
  Proof. unfold beta_reduction; now tm_simpl. Qed.

  Theorem beta_reduction_other m t :
    tm_other t -> beta_reduction m t = t.
  Proof.
    intros. unfold beta_reduction. now tm_simpl.
  Qed.

  Hint Rewrite beta_reduction_app_abs beta_reduction_abs : tm.
  Hint Rewrite beta_reduction_other using assumption : tm.


  Definition eta_reduction m (t : tm) : tm :=
    (fix fx m t :=
    match t with
    | tmv_lvl n => tm_lvl n
    | tmv_abs T (tmv_app t (tmv_lvl n)) =>
        if andb (eqb n m) (negb (contains_bound_levels m 1 (to_tm t))) then
          bound_level_map (fun x => x - 1) m (to_tm t)
          else tm_abs T (tm_app (fx (S m) t) (tm_lvl n))
    | tmv_app s t => tm_app (fx m s) (fx m t)
    | tmv_abs T t => tm_abs T (fx (S m) t)
    | tmv_other t => t
    end) m (to_tmv t).

  Theorem eta_reduction_lvl m n:
    eta_reduction m (tm_lvl n) = tm_lvl n.
  Proof. unfold eta_reduction; now tm_simpl. Qed.

  Theorem eta_reduction_app m s t :
    eta_reduction m (tm_app s t) = tm_app (eta_reduction m s) (eta_reduction m t).
  Proof. unfold eta_reduction; now tm_simpl. Qed.

  Theorem eta_reduction_abs_app m T t:
    contains_bound_levels m 1 t = false ->
    eta_reduction m (tm_abs T (tm_app t (tm_lvl m))) =
    bound_level_map (fun x => x - 1) m t.
  Proof.
    intros.
    unfold eta_reduction. tm_simpl.
    rewrite eqb_refl. now rewrite H.
  Qed.

  Theorem eta_reduction_abs_app2 m t T :
    contains_bound_levels m 1 t = true ->
    eta_reduction m (tm_abs T (tm_app t (tm_lvl m))) =
    tm_abs T (tm_app (eta_reduction (S m) t) (tm_lvl m)).
  Proof.
    intros. unfold eta_reduction. tm_simpl.
    rewrite eqb_refl. now rewrite H.
  Qed.

  Theorem eta_reduction_abs_app3 m n t T :
    n <> m ->
    eta_reduction m (tm_abs T (tm_app t (tm_lvl n))) =
    tm_abs T (tm_app (eta_reduction (S m) t) (tm_lvl n)).
  Proof.
    intros. unfold eta_reduction. tm_simpl.
    destruct (eqb_spec n m); [lia|].
    reflexivity.
  Qed.

  Theorem eta_reduction_abs m T t :
    (forall a, t <> tm_app a (tm_lvl m)) ->
    eta_reduction m (tm_abs T t) = tm_abs T (eta_reduction (S m) t).
  Proof.
    intros N.
    destruct t using tm_ind; unfold eta_reduction; tm_simpl; try reflexivity.
    destruct t2 using tm_ind; tm_simpl; try reflexivity.
    destruct (eqb_spec n m).
    - subst. exfalso. now eapply N.
    - auto.
  Qed.

  Hint Rewrite eta_reduction_app : tm.


  Theorem has_type_beta_reduction C T t :
    has_type C t T ->
    has_type C (beta_reduction |(C)| t) T.
  Proof.
    generalize dependent T. generalize dependent C.
    induction t using tm_ind; intros C A HT.
    - unfold beta_reduction; now tm_simpl.
    - tm_simpl. destruct HT as (B & Ht1 & Ht2).
      assert (D : (forall T t, t1 <> tm_abs T t) \/ exists T t, t1 = tm_abs T t). {
        destruct t1 using tm_ind; try (left; intros * ?; tm_discriminate).
        right. eauto.
      }
      destruct D.
      + rewrite beta_reduction_app; [|auto].
        tm_simplg. exists B. split; auto.
      + destruct H as (T & t & Ht). subst. tm_simplg.
        eapply has_type_subst_last; [|eauto].
        apply IHt1 in Ht1 as F. tm_simpl.
        destruct F as (D & HD1 & HD2).
        apply ty_arr_inj in HD2. destruct HD2. now subst.
    - tm_simpl.
      destruct HT as (B & HB1 & HB2).
      eexists. split; [|eassumption].
      replace (S |(C)|) with |(C +: T)|; [|now rewrite rlength_rcons].
      now apply IHt.
    - now tm_simpl.
  Qed.

  Theorem has_type_eta_reduction C T t :
    has_type C t T ->
    has_type C (eta_reduction |(C)| t) T.
  Proof.
    generalize dependent T. generalize dependent C.
    induction t using tm_ind; intros C A HT.
    - unfold eta_reduction; now tm_simpl.
    - tm_simpl. destruct HT as (B & HB1 & HB2).
      exists B. split; auto.
    - tm_simpl. destruct HT as (B & HB1 & HB2).
      assert (D : (forall a n, t0 <> tm_app a (tm_lvl n)) \/ exists a n, t0 = tm_app a (tm_lvl n)). {
        destruct t0 using tm_ind; try (left; intros * ?; tm_discriminate).
        destruct t0_2 using tm_ind; try (left; intros * ?; tm_discriminate).
        - right. eauto.
        - left. intros * N. tm_injection N. intros.
          apply (f_equal to_tm) in H0. tm_simpl. tm_discriminate.
      }
      destruct D.
      + rewrite eta_reduction_abs; [|auto].
        tm_simplg. exists B. split; [|assumption].
        apply IHt in HB1. now rewrite rlength_rcons in HB1.
      + destruct H as (a & n & Ha). subst.
        destruct (eqb_spec n |(C)|).
        * subst.
          destruct (contains_bound_levels |(C)| 1 a) eqn : E.
          -- rewrite eta_reduction_abs_app2; [|assumption].
             tm_simplg. exists B. split; [|reflexivity].
             apply IHt in HB1. rewrite rlength_rcons in HB1.
             now rewrite eta_reduction_app, eta_reduction_lvl in HB1.
          -- rewrite eta_reduction_abs_app; [|assumption].
             apply (has_type_bound_level_map2 1 _ (C +: T)).
             ++ now rewrite rlength_rcons.
             ++ intros n Hn. lookup_rcons_spec C T n H F; try reflexivity; lia.
             ++ tm_simpl1 HB1.
                rewrite bound_level_map_id; auto.
                destruct HB1 as (A & HA1 & HA2).
                tm_simpl. rewrite @lookup_rcons_eq in HA2; [|reflexivity].
                injection HA2. now intros ->.
        * rewrite eta_reduction_abs_app3; [|assumption].
          tm_simplg. exists B. split; [|reflexivity].
           apply IHt in HB1. rewrite rlength_rcons in HB1.
           now rewrite eta_reduction_app, eta_reduction_lvl in HB1.
    - unfold eta_reduction. now tm_simpl.
  Qed.
End StlcTheories.
