Require Export stlc_types.
From stdpp Require Export relations.

Import Lia PeanoNat.Nat.


(***********************************)
(** * Simply Typed Lambda Calculus *)
(***********************************)


(*****************)
(** ** Interface *)
(*****************)

Declare Custom Entry stlc_tm.

Module Type STLC.
  Declare Module Ty : TY.
  Module TyTheories := TyTheories Ty.
  Export TyTheories.


  (** *** Terms *)

  Parameter tm : Set.
  Parameter tm_lvl : nat -> tm.
  Parameter tm_app : tm -> tm -> tm.
  Parameter tm_abs : ty -> tm -> tm.
  Parameter tm_other : tm -> Prop.

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


  Parameter type_check_other : tm -> ty.
End STLC.


(****************)
(** ** Theories *)
(****************)

Module StlcTheories (Stlc : STLC).
  Export Stlc.


  (** *** Terms *)

  Coercion tm_lvl : nat >-> tm.

  Definition tm_rec (P : tm -> Set) := tm_rect P.
  Definition tm_ind (P : tm -> Prop) := tm_rect P.

  (** Tactics *)
  Create HintDb tm.
  Hint Rewrite tm_rect_lvl tm_rect_app tm_rect_abs : tm.
  Hint Rewrite tm_rect_other using assumption : tm.
  Tactic Notation "tm_simpl" := repeat (autorewrite with tm; simpl).
  Tactic Notation "tm_simpl" "in" ident(H) := repeat (simpl in H; autorewrite with tm in H).
  Tactic Notation "tm_simpl" "in" "*" := repeat (simpl in *; autorewrite with tm in *).
  Ltac tm_induction t := induction t using tm_ind.


  (** tm_other terms are distinct from tm_lvl, tm_app and tm_abs *)

  Theorem tm_other_lvl n : ~ tm_other (tm_lvl n).
  Proof.
    intros N.
    set (f := tm_rect _ (fun _ => false) (fun _ _ _ _ => false) (fun _ _ _ => false) (fun _ _ => true)).
    assert (f n = f n); [reflexivity|].
    subst f.
    rewrite tm_rect_lvl in H at 1.
    rewrite tm_rect_other in H; easy.
  Qed.

  Theorem tm_other_app s t : ~ tm_other (tm_app s t).
  Proof.
    intros N.
    set (f := tm_rect _ (fun _ => false) (fun _ _ _ _ => false) (fun _ _ _ => false) (fun _ _ => true)).
    assert (f (tm_app s t) = f (tm_app s t)); [reflexivity|].
    subst f.
    rewrite tm_rect_app in H at 1.
    rewrite tm_rect_other in H; easy.
  Qed.

  Theorem tm_other_abs T t : ~ tm_other (tm_abs T t).
  Proof.
    intros N.
    set (f := tm_rect _ (fun _ => false) (fun _ _ _ _ => false) (fun _ _ _ => false) (fun _ _ => true)).
    assert (f (tm_abs T t) = f (tm_abs T t)); [reflexivity|].
    subst f.
    rewrite tm_rect_abs in H at 1.
    rewrite tm_rect_other in H; easy.
  Qed.


  (** Inductive type view *)

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
    tm_induction t; tm_simpl; congruence.
  Qed.

  Hint Rewrite to_tm_to_tmv : tm.


  (** discriminate and injection for tm *)

  Ltac to_tmv H := apply (f_equal to_tmv) in H; tm_simpl in H.
  Ltac to_tm H :=
    match type of H with
    | to_tmv ?x = to_tmv ?y => apply (f_equal to_tm) in H; repeat rewrite to_tm_to_tmv in H
    end.
  Tactic Notation "to_tm" := match goal with | [H : _ |- _] => to_tm H end.
  Ltac tm_discriminate H :=
    match type of H with
    | tm_other (tm_lvl ?n) => exfalso; now apply (tm_other_lvl n)
    | tm_other (tm_app ?s ?t) => exfalso; now apply (tm_other_app s t)
    | tm_other (tm_abs ?T ?t) => exfalso; now apply (tm_other_abs T t)
    | _ => to_tmv H; discriminate H
    end.
  Tactic Notation "tm_discriminate" ident(H) := tm_discriminate H.
  Tactic Notation "tm_discriminate" :=
    match goal with | [H : _ |- _] => tm_discriminate H end.
  Ltac tm_injection H := to_tmv H; injection H; intros; repeat to_tm; subst.


  (**************)
  (** ** Typing *)
  (**************)

  Inductive has_type : context -> tm -> ty -> Prop :=
    | ht_lvl (c : context) n : n < c -> has_type c (tm_lvl n) (c n)
    | ht_app c A B s t : has_type c s (ty_arr A B) -> has_type c t A ->
        has_type c (tm_app s t) B
    | ht_abs c A B t : has_type (c +: A) t B ->
        has_type c (tm_abs A t) (ty_arr A B)
    | ht_other c t : tm_other t -> has_type c t (type_check_other t).

  Theorem ht_other2 c T t :
    tm_other t -> T = type_check_other t ->
    has_type c t T.
  Proof. intros ? ->. now constructor. Qed.

  Theorem has_type_lvl : forall c n T,
    has_type c (tm_lvl n) T <-> n < c /\ c n = T.
  Proof.
    split; intros.
    - inversion H; try tm_discriminate; subst.
      tm_injection H0. split; congruence.
    - destruct H. subst. now constructor.
  Qed.

  Theorem has_type_app : forall c s t B,
    has_type c (tm_app s t) B <->
    exists2 A, has_type c s (ty_arr A B) &  has_type c t A.
  Proof.
    split; intros.
    - inversion H; subst; try tm_discriminate.
      tm_injection H0. now exists A.
    - destruct H. econstructor; eauto.
  Qed.

  Theorem has_type_abs : forall c A T t,
    has_type c (tm_abs A t) T <->
    exists2 B, has_type (c +: A) t B & T = -[ A -> B ]-.
  Proof.
    split; intros.
    - inversion H; subst; try tm_discriminate.
      tm_injection H0. now exists B.
    - destruct H. subst. now constructor.
  Qed.

  Theorem has_type_other c t T :
    tm_other t ->
    has_type c t T <-> type_check_other t = T.
  Proof.
    split; intros.
    - inversion H0; subst; try tm_discriminate. reflexivity.
    - subst. now constructor.
  Qed.

  Hint Rewrite has_type_lvl has_type_app has_type_abs : tm.
  Hint Rewrite has_type_other using assumption : tm.


  Theorem has_type_unique c t A B :
    has_type c t A -> has_type c t B -> A = B.
  Proof.
    revert B A c.
    tm_induction t; intros c A B HA HB; tm_simpl in *;
      (try intuition congruence); destruct HA, HB.
    - eapply IHt1 in H; [|eassumption]. now ty_injection H.
    - subst. f_equal. eauto.
  Qed.


  (**************************)
  (** ** Level manipulation *)
  (**************************)

  Definition level_prop (P : nat -> Prop) t : Prop :=
    (fix fx P t :=
      match t with
      | tmv_lvl m => P m
      | tmv_abs T s => fx P s
      | tmv_app s1 s2 => fx P s1 \/ fx P s2
      | _ => False
    end) P (to_tmv t).

  Theorem level_prop_lvl P (n : nat) : level_prop P n <-> P n.
  Proof. unfold level_prop. now tm_simpl. Qed.

  Theorem level_prop_app P s t :
    level_prop P (tm_app s t) <-> level_prop P s \/  level_prop P t.
  Proof. unfold level_prop. tm_simpl. auto. Qed.

  Theorem level_prop_abs P T t :
    level_prop P (tm_abs T t) <-> level_prop P t.
  Proof. unfold level_prop. now tm_simpl. Qed.

  Theorem level_prop_other P t : tm_other t -> ~ level_prop P t.
  Proof. intros. unfold level_prop. now tm_simpl. Qed.

  Hint Rewrite level_prop_lvl level_prop_app level_prop_abs : tm.

  Definition contains_bound_levels m n :=
    level_prop (fun x => m <= x /\ x < (n + m)).


  (** Apply "f" to all variables in the term "t" *)
  Definition level_map (f : nat -> nat) (t : tm) : tm :=
    (fix fx f x :=
      match x with
      | tmv_lvl n => tm_lvl (f n)
      | tmv_app a b => tm_app (fx f a) (fx f b)
      | tmv_abs T t => tm_abs T (fx f t)
      | tmv_other t => t
    end) f (to_tmv t).

  Theorem level_map_lvl f n : level_map f (tm_lvl n) = f n.
  Proof. unfold level_map. now tm_simpl. Qed.

  Theorem level_map_app f s t :
    level_map f (tm_app s t) = tm_app (level_map f s) (level_map f t).
  Proof. unfold level_map. now tm_simpl. Qed.

  Theorem level_map_abs f T t :
    level_map f (tm_abs T t) = tm_abs T (level_map f t).
  Proof. unfold level_map. now tm_simpl. Qed.

  Theorem level_map_other f t :
    tm_other t -> level_map f t = t.
  Proof. intros. unfold level_map. now tm_simpl. Qed.

  Hint Rewrite level_map_lvl level_map_app level_map_abs : tm.
  Hint Rewrite level_map_other using assumption : tm.

  Theorem level_map_f_eq f g t :
    (forall n, f n = g n) -> level_map f t = level_map g t.
  Proof.
    intros H. tm_induction t; tm_simpl; congruence.
  Qed.

  (*
  Definition free_level_map f m :=
    level_map (fun n => if decide (n < m) then f n else n).

  Theorem has_type_free_level_map f c d t T :
    rl_length c = |(d)| -> (forall n, d !! f n = c !! n) ->
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
    - assumption.
  Qed.
  *)


  (** Apply "f" to all bound variables in the term "t" *)
  Definition bound_level_map f m :=
    level_map (fun n => if decide (m <= n) then f n else n).

  Definition lift := bound_level_map S.

  Theorem has_type_bound_level_map_h l m (c d : context) t T :
    l <= c -> rl_length d = m + c ->
    (forall n, n >= l -> n < c -> d (m + n) = c n) ->
    (forall n, n < l -> d n = c n) ->
    has_type c t T <->
    has_type d (bound_level_map (add m) l t) T.
  Proof.
    revert c d T.
    tm_induction t; intros c d A Hl L Hlg Hll;
      unfold bound_level_map in *; tm_simpl.
    - destruct (decide (l <= n)), (decide (n < c)).
      + rewrite Hlg; try easy. split; intuition; lia.
      + split; intuition lia.
      + rewrite Hll; [|lia]. split; intuition; lia.
      + split; intuition lia.
    - split; intros [B]; exists B;
        first [eapply IHt1 | eapply IHt2]; eauto.
    - split; intros [B]; exists B; try assumption.
      + apply (IHt (c +: T)); try assumption; try intros n Hn; simpl; try lia.
        * destruct (decide (m + n < d)), (decide (n < c)); auto; intros; lia.
        * destruct (decide (n < d)), (decide (n < c)); auto; lia.
      + eapply (IHt (c +: T)); try eassumption; try intros n Hn; simpl; try lia.
        * destruct (decide (m + n < d)), (decide (n < c)); auto; lia.
        * destruct (decide (n < d)), (decide (n < c)); auto; lia.
    - auto.
  Qed.

  Theorem has_type_bound_level_map1 m (c d : context) t T :
    rl_length d = m + c ->
    (forall n, n < c -> d n = c n) ->
    has_type c t T ->
    has_type d (bound_level_map (add m) c t) T.
  Proof.
    intros. rewrite <- has_type_bound_level_map_h; try eassumption; lia.
  Qed.

  Theorem has_type_lift1 C c t T :
    has_type C t T ->
    has_type (C +: c) (lift C t) T.
  Proof.
    intros Ht. apply (has_type_bound_level_map1 1); simpl; try easy.
    intros. now rewrite decide_True.
  Qed.

  Theorem has_type_bound_level_map2 m (c d : context) t T :
    rl_length d = m + c ->
    (forall n, n < c -> d n = c n) ->
    has_type d (bound_level_map (add m) c t) T ->
    has_type c t T.
  Proof.
    intros. eapply has_type_bound_level_map_h; try eassumption; lia.
  Qed.

  (*
  Theorem has_type_bound_level_map m (c d : context) t T :
    rl_length d = m + c ->
    (forall n, n < c -> d n = c n) ->
    has_type c t T <->
    has_type d (bound_level_map (add m) c t) T.
  Proof.
    split; intros.
    - now apply has_type_bound_level_map1.
    - eapply has_type_bound_level_map2; eassumption.
  Qed.
  *)

  Theorem has_type_lift2 C c t T :
    has_type (C +: c) (lift C t) T -> has_type C t T.
  Proof.
    intros Ht.
    eapply (has_type_bound_level_map2 1); try eassumption; simpl; try easy.
    intros. now rewrite decide_True.
  Qed.

  Theorem bound_level_map_id m n t :
    ~ contains_bound_levels m n t ->
    bound_level_map (add n) m (bound_level_map (fun x => x - n) m t) = t.
  Proof.
    unfold bound_level_map, contains_bound_levels.
    intros L. tm_induction t; tm_simpl in *.
    - f_equal.
      destruct (decide (m <= n0)), (decide (m <= n0 - n)); try lia.
      destruct (decide (m <= n0)); lia.
    - intuition congruence.
    - intuition congruence.
    - rewrite (level_map_other _ t0) by assumption.
      now tm_simpl.
  Qed.


  (********************)
  (** ** Substitution *)
  (********************)

  (** Parallel substitution *)
  Definition subst m l t :=
    (fix fx m l t :=
      match t with
      | tmv_lvl n => lookup_default (tm_lvl n) n l
      | tmv_app a b => tm_app (fx m l a) (fx m l b)
      | tmv_abs T t => tm_abs T (fx (S m) ((lift m <$> l) +: tm_lvl m) t)
      | tmv_other t => t
    end) m l (to_tmv t).

  Theorem subst_lvl m l n :
    subst m l (tm_lvl n) = lookup_default (tm_lvl n) n l.
  Proof. unfold subst. now tm_simpl. Qed.

  Theorem subst_app m l s t :
    subst m l (tm_app s t) = tm_app (subst m l s) (subst m l t).
  Proof. unfold subst. now tm_simpl. Qed.

  Theorem subst_abs m l T t :
    subst m l (tm_abs T t) = tm_abs T (subst (S m) ((lift m <$> l) +: tm_lvl m) t).
  Proof. unfold subst. now tm_simpl. Qed.

  Theorem subst_other m l t : tm_other t -> subst m l t = t.
  Proof. intros. unfold subst. now tm_simpl. Qed.

  Hint Rewrite subst_lvl subst_app subst_abs : tm.
  Hint Rewrite subst_other using easy : tm.


  Instance subst_Proper m : Proper ((≡) ==> (=) ==> (=)) (subst m).
  Proof.
    intros x y E ? t ->.
    revert m x y E.
    tm_induction t; intros m x y E; tm_simpl.
    - unfold lookup_default. destruct E. rewrite H in *.
      destruct (decide (n < y)); auto.
    - now erewrite IHt1, IHt2.
    - f_equal. apply IHt. now rewrite E.
    - reflexivity.
  Qed.

  Theorem has_type_subst1 C T R t r :
    rl_length r = rl_length R ->
    (forall n, n < r -> has_type C (r n) (R n)) ->
    has_type R t T -> has_type C (subst C r t) T.
  Proof.
    revert C T R r.
    tm_induction t; intros C A R r L F HT; tm_simpl in *.
    - unfold lookup_default. destruct HT.
      rewrite  <- L in H. rewrite decide_True; [|easy].
      subst. auto.
    - destruct HT as [B]. exists B; eauto.
    - destruct HT as [B]. exists B; [|easy].
      replace (S C) with (rl_length (C +: T)); [|reflexivity].
      eapply IHt; try eassumption.
      + simpl. congruence.
      + simpl. intros. rewrite L. destruct (decide (n < R)).
        * apply has_type_lift1. apply F. lia.
        * tm_simpl. rewrite decide_False; intuition lia.
    - assumption.
  Qed.

  Theorem has_type_subst2 (C R : context) T t r :
    C <= R -> rl_length r = R ->
    (forall n, n < r -> has_type C (r n) (R n)) ->
    has_type C (subst C r t) T -> has_type R t T.
  Proof.
    revert C T R r.
    tm_induction t; tm_simpl; intros C A R r L E F HT.
    - assert (HT1 := HT). unfold subst in HT; tm_simpl in HT.
      assert (exists A, has_type R n A). {
        destruct (decide (n < R)) as [Hn | Hn].
        - exists (R n). tm_simpl. intuition.
        - unfold lookup_default in HT.
          destruct (decide (n < r)); try lia.
          tm_simpl in *. destruct HT. lia.
      }
      destruct H as [X H]. replace A with X; [assumption|].
      eapply has_type_subst1 in H; try eassumption.
      eapply has_type_unique; eassumption.
    - tm_simpl in *.
      destruct HT as [B]. exists B; eauto.
    - tm_simpl in *.
      destruct HT as [B]. exists B; [|assumption].
      eapply (IHt (C +: T)).
      4:{
        replace (S C) with (rl_length (C +: T)) in H; [|reflexivity].
        apply H.
      }
      + simpl. lia.
      + simpl. congruence.
      + intros. simpl in *. rewrite E. destruct (decide (n < R)).
        * apply has_type_lift1. apply F. lia.
        * tm_simpl. rewrite decide_False; intuition lia.
    - now tm_simpl in *.
  Qed.

  Theorem has_type_subst (C R : context) T t r :
    C <= R -> rl_length r = R ->
    (forall n, n < r -> has_type C (r n) (R n)) ->
    has_type C (subst C r t) T <-> has_type R t T.
  Proof.
    split; intros.
    - eapply has_type_subst2; eassumption.
    - eapply has_type_subst1; eassumption.
  Qed.


  Definition subst_last m n s := subst n (Build_rlist m tm_lvl +: s).

  Notation "[ n ; m | s ] t" := (subst_last n m s t) (in custom stlc_tm at level 5) : stlc_scope.
  Notation "[ n | s ] t" := (subst_last n n s t) (in custom stlc_tm at level 5) : stlc_scope.

  Theorem subst_last_app m n s a b :
    subst_last m n s (tm_app a b) =
    tm_app (subst_last m n s a) (subst_last m n s b).
  Proof. unfold subst_last. now tm_simpl. Qed.

  Theorem subst_last_other m n s t : tm_other t -> subst_last m n s t = t.
  Proof. intros. unfold subst_last. now tm_simpl. Qed.

  Hint Rewrite subst_last_app : tm.
  Hint Rewrite subst_last_other using easy : tm.


  Theorem has_type_subst_last1 (C D : context) T X s t :
    C <= D ->
    (forall n, n < C -> C n = D n) ->
    has_type D s T ->
    has_type (C +: T) t X -> has_type D (subst_last C D s t) X.
  Proof.
    intros ? E **. eapply has_type_subst1; try eassumption; try reflexivity.
    intros. simpl in *. destruct (decide (n < C)); try easy.
    rewrite E by assumption. tm_simpl. intuition lia.
  Qed.

  Theorem has_type_subst_last_s1 (C : context) T X s t :
    has_type C s T ->
    has_type (C +: T) t X -> has_type C (subst_last C C s t) X.
  Proof. intros. eapply has_type_subst_last1; eauto. Qed.

  Theorem has_type_subst_last2 (C D : context) T X s t :
    C <= D -> D <= S C ->
    (forall n, n < C -> C n = D n) ->
    has_type D s T ->
    has_type D (subst_last C D s t) X -> has_type (C +: T) t X.
  Proof.
    intros ? ? HD Hs Ht. eapply has_type_subst2; try eassumption; try reflexivity.
    intros. simpl in *. destruct (decide (n < C)); try easy.
    rewrite HD by assumption. tm_simpl. intuition lia.
  Qed.

  Theorem has_type_subst_last_s2 (C : context) T X s t :
    has_type C s T ->
    has_type C (subst_last C C s t) X ->
    has_type (C +: T) t X.
  Proof. intros. eapply has_type_subst_last2; eauto. Qed.

  (*
  Theorem has_type_subst_last C T X s t :
    has_type C s T ->
    has_type (C +: T) t X <-> has_type C (subst_last |(C)| s t) X.
  Proof.
    intros Hs.
    unfold subst_last. rewrite has_type_subst.
    - split; intros H; apply H.
    - rewrite rlength_rcons. lia.
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
  *)


  (*****************)
  (** ** Reduction *)
  (*****************)

  Definition preserves_type (c : nat -> tm -> tm -> Prop) :=
    forall (C : context) T a b, c C a b ->
    has_type C a T -> has_type C b T.

  Inductive step c m : tm -> tm -> Prop :=
    | step_conv a b : c m a b -> step c m a b
    | step_appL a b t : step c m a b -> step c m (tm_app a t) (tm_app b t)
    | step_appR s a b : step c m a b -> step c m (tm_app s a) (tm_app s b)
    | step_abs T a b : step c (S m) a b -> step c m (tm_abs T a) (tm_abs T b).

  Definition reduces c m := rtc (step c m).
  Definition conv_eq c m := rtsc (step c m).

  Theorem has_type_step c (C : context) T a b :
    preserves_type c -> step c C a b ->
    has_type C a T -> has_type C b T.
  Proof.
    intros Hc BS. remember (rl_length C) as l.
    revert T. generalize dependent C.
    induction BS; intros C Hl A HT; tm_simpl in *.
    - subst. unfold preserves_type in *. eauto.
    - destruct HT as [B]. exists B; auto.
    - destruct HT as [B]. exists B; auto.
    - destruct HT as [B]. exists B; [|easy].
      apply IHBS; simpl; congruence.
  Qed.


  Inductive beta_conv m : tm -> tm -> Prop :=
    beta_conv_intro T t s :
      beta_conv m (tm_app (tm_abs T t) s) (subst_last m m s t).

  Theorem has_type_beta_conv : preserves_type beta_conv.
  Proof.
    unfold preserves_type. intros * HB **.
    destruct HB. tm_simpl in *. destruct H. tm_simpl in *. destruct H.
    ty_injection H1.
    eapply has_type_subst_last1; try eassumption; try easy.
  Qed.


  Inductive eta_conv m : tm -> tm -> Prop :=
    eta_conv_intro T t :
        ~ contains_bound_levels m 1 t ->
        eta_conv m (tm_abs T (tm_app t m)) (bound_level_map (fun x => x - 1) m t).

  Theorem has_type_eta_conv : preserves_type eta_conv.
  Proof.
    unfold preserves_type. intros * HE **.
    destruct HE. tm_simpl in *. destruct H. tm_simpl in *. destruct H.
    subst. apply (has_type_bound_level_map2 1 _ (C +: T0)); try easy.
    - intros. simpl. now rewrite decide_True.
    - rewrite bound_level_map_id; try easy.
      tm_simpl in *. rewrite decide_False in * by lia. intuition congruence.
  Qed.


  (*
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
        eapply has_type_subst_last; [eauto|].
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
  *)


  Definition lambda_equiv m :=
    conv_eq (fun m a b => beta_conv m a b \/ eta_conv m a b) m.

  (*
  Inductive lambda_equiv m : tm -> tm -> Prop :=
    | le_id t : lambda_equiv m t t
    | le_beta a b c :
        lambda_equiv m a b -> step beta_conv m b c -> lambda_equiv m a c
    | le_eta a b c :
        lambda_equiv m a b -> step eta_conv m b c -> lambda_equiv m a c.

  Theorem th {A} (R : relation A) a b :
    Equivalence R -> rtsc R a b <-> R a b.
  Proof.
    intros E. split; intros H.
    - unfold rtsc in H. remember (sc R) as scR.
      induction H; subst.
      + now destruct E.
      + destruct H.
        * destruct E. eauto.
        * destruct E. eauto.
    - now apply rtsc_lr.
  Qed.


  Theorem has_type_lambda_equiv (C : context) T a b :
    lambda_equiv C a b ->
    has_type C a T -> has_type C b T.
  Proof.
    Search rtc.
    intros LE HT.
    induction LE; try easy.
    - eapply has_type_step; eauto.
      intros D A a b R Ha. destruct R.
      + eapply has_type_beta_conv; eassumption.
      + eapply has_type_eta_conv; eassumption.
    -
    - apply has_type_beta_conv.
    - apply has_type_eta_conv.
  Qed.
  *)
End StlcTheories.
