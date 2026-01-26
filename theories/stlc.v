From Coq Require Export List.
From stdpp Require Import decidable.


(***********************************)
(** * Simply Typed Lambda Calculus *)
(***********************************)


(**************)
(** ** Syntax *)
(**************)


(** *** Types *)

(** Interface for the types of stlc.  There must be a type for propositions and
    an arrow type. *)
Module Type TY.
  Parameter ty : Set.
  Parameter ty_prp : ty.
  Parameter ty_arr : ty -> ty -> ty.

  Declare Instance eq_ty_dec : EqDecision ty.

  Parameter ty_rec :
    forall P : ty -> Set,
      P ty_prp ->
      (forall t, P t -> forall s, P s -> P (ty_arr t s)) ->
      (forall t, P t) ->
      forall t, P t.

  Axiom ty_rec_prp : forall P p a d, ty_rec P p a d ty_prp = p.
  Axiom ty_rec_arr : forall P p a d A B,
    ty_rec P p a d (ty_arr A B) = a _ (ty_rec P p a d A) _ (ty_rec P p a d B).
End TY.

(** Global notation declarations. *)
Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.
Declare Custom Entry stlc_ty.

Module TyTheories (Ty : TY).
  Export Ty.

  Definition context := list ty.

  Notation "<[ x ]>" := x (x custom stlc_ty) : stlc_scope.
  Notation "x" := x (in custom stlc_ty at level 0, x global) : stlc_scope.
  Notation "A -> B" := (ty_arr A B)
    (in custom stlc_ty at level 99, right associativity) : stlc_scope.
  Notation "( t )" := t
    (in custom stlc_ty at level 0, t custom stlc_ty) : stlc_scope.
  Notation "'o'" := ty_prp (in custom stlc_ty at level 0) : stlc_scope.
End TyTheories.

Module TyChurch <: TY.
  Inductive tyc : Set :=
    | tyc_prp : tyc
    | tyc_obj : tyc
    | tyc_arr : tyc -> tyc -> tyc.
  Print tyc_rect.
  Check tyc_rec (fun t => nat).

  Definition ty := tyc.
  Definition ty_prp := tyc_prp.
  Definition ty_arr := tyc_arr.

  Instance eq_ty_dec : EqDecision ty.
  Proof. solve_decision. Qed.

  Fixpoint eqb_ty S T :=
    match S, T with
    | tyc_arr A1 B1, tyc_arr A2 B2 => andb (eqb_ty A1 A2) (eqb_ty B1 B2)
    | tyc_prp, tyc_prp => true
    | tyc_obj, tyc_obj => true
    | _, _ => false
    end.
  
  Theorem eqb_ty_eq A B : eqb_ty A B = true -> A = B.
  Proof.
    generalize dependent B.
    induction A; simpl in *; destruct B;
      try discriminate; try reflexivity.
    intros H. erewrite IHA1, IHA2.
    - reflexivity.
    - destruct (eqb_ty A2 B2); try reflexivity.
      rewrite Bool.andb_false_r in H. discriminate.
    - destruct (eqb_ty A1 B1); try reflexivity.
      simpl in *. discriminate.
  Qed.

  Definition ty_rec :
    forall P : ty -> Set,
      P ty_prp ->
      (forall t, P t -> forall s, P s -> P (ty_arr t s)) ->
      (forall t, P t) ->
      forall t, P t :=
      fun P p a d => tyc_rec P p (d tyc_obj) a.

  Theorem ty_rec_prp P p a d : ty_rec P p a d ty_prp = p.
  Proof. reflexivity. Qed.

  Theorem eqb_ty_spec A B : reflect (A = B) (eqb_ty A B).
  Proof.
    generalize dependent B.
    induction A; simpl in *; destruct B;
      try constructor; try discriminate; try reflexivity.
    destruct (IHA1 B1), (IHA2 B2); subst; constructor;
      try (intros E; injection E; auto).
    reflexivity.
  Qed.

  Definition is_ty_arr t :=
    match t with
    | tyc_arr A B => Some (A, B)
    | _ => None
    end.

  Theorem is_ty_arr_ty_arr A B :
    is_ty_arr (ty_arr A B) = Some (A, B).
  Proof. reflexivity. Qed.

  Theorem ty_arr_is_ty_arr A B t :
    is_ty_arr t = Some (A, B) -> t = ty_arr A B.
  Proof.
    intros H. destruct t; simpl in *; try discriminate.
    injection H. intros. subst. reflexivity.
  Qed.

  Theorem ty_rec_arr P p a d A B :
    ty_rec P p a d (ty_arr A B) =
    a _ (ty_rec P p a d A) _ (ty_rec P p a d B).
  Proof. reflexivity. Qed.
End TyChurch.

Module TyChurchTheories.
  Module TyTheories := TyTheories TyChurch.
  Import TyTheories.

  Notation "'i'" := tyc_obj (in custom stlc_ty at level 0) : stlc_scope.

  (** Examples *)
  Check <[ o ]>.
  Check <[ o -> i ]>.
  Check <[ o -> (i -> o) ]>.
  Check <[ (o -> i) -> o ]>.
End TyChurchTheories.


(** *** Terms *)

Declare Custom Entry stlc_tm.

Module Stlc (Ty : TY).
  Module TyTheories := TyTheories Ty.
  Export TyTheories.

  (** Terms using de Bruijn levels *)
  Inductive tm : Set :=
    | tm_lvl : nat -> tm
    | tm_app : tm -> tm -> tm
    | tm_abs : ty -> tm -> tm
    | tm_bot : tm
    | tm_top : tm
    | tm_and : tm
    | tm_or  : tm
    | tm_imp : tm
    | tm_for : ty -> tm
    | tm_ex  : ty -> tm.

  (** Notations *)
  Notation "<{ x }>" := x (x custom stlc_tm at level 200) : stlc_scope.
  Notation "x" := x
    (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
  Notation "( t )" := t
    (in custom stlc_tm at level 0, t custom stlc_tm) : stlc_scope.
  Notation "$( x )" := x
    (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
  Notation "x y" := (tm_app x y)
    (in custom stlc_tm at level 10, left associativity) : stlc_scope.
  Notation "\: A , t" := (tm_abs A t)
    (in custom stlc_tm at level 200, A custom stlc_ty,
    t custom stlc_tm at level 200, left associativity) : stlc_scope.
  Notation "_|" := (tm_bot)
    (in custom stlc_tm at level 0) : stlc_scope.
  Notation "^|" := (tm_top)
    (in custom stlc_tm at level 0) : stlc_scope.
  Notation "x /\ y" := (tm_and x y)
    (in custom stlc_tm at level 50, left associativity) : stlc_scope.
  Notation "x \/ y" := (tm_or x y)
    (in custom stlc_tm at level 60, left associativity) : stlc_scope.
  Notation "x > y" := (tm_imp x y)
    (in custom stlc_tm at level 70, left associativity) : stlc_scope.
  Coercion tm_lvl : nat >-> tm.

  (** Examples *)
  Check fun x : ty => <{ \: x, 0 }>.
  Check fun x : ty => <{ (\: (x -> o), 2) 1 }>.
  Check <{ \: o, 3 _| }>.


  (**************)
  (** ** Typing *)
  (**************)

  Inductive has_type : context -> tm -> ty -> Prop :=
    | t_lvl c n T : nth_error c n = Some T -> has_type c n T
    | t_abs c A B t : has_type (c ++ [A]) t B ->
        has_type c (tm_abs A t) (ty_arr A B)
    | t_app c A B s t : has_type c s (ty_arr A B) -> has_type c t A ->
        has_type c (tm_app s t) B
    | t_bot c : has_type c tm_bot ty_prp
    | t_top c : has_type c tm_top ty_prp
    | t_and c : has_type c tm_and <[ o -> o -> o ]>
    | t_or  c : has_type c tm_or  <[ o -> o -> o ]>
    | t_imp c : has_type c tm_imp <[ o -> o -> o ]>
    | t_for c T : has_type c (tm_for T) <[ (T -> o) -> o ]>
    | t_ex  c T : has_type c (tm_ex  T) <[ (T -> o) -> o ]>.

  Fixpoint type_check (c : context) (t : tm) : option ty :=
    match t with
    | tm_lvl n => nth_error c n
    | tm_abs A t =>
        match type_check (c ++ [A]) t with
        | Some B => Some <[ A -> B ]>
        | _ => None
        end
    | tm_app s t =>
        match type_check c s, type_check c t with
        | Some AR, Some A1 =>
            ty_rec _ None (fun A _ B _ => if decide (A = A1) then Some B else None) (fun t => None) AR
        | _, _ => None
        end
    | tm_bot => Some ty_prp
    | tm_top => Some ty_prp
    | tm_and => Some <[ o -> o -> o ]>
    | tm_or  => Some <[ o -> o -> o ]>
    | tm_imp => Some <[ o -> o -> o ]>
    | tm_for T => Some <[ (T -> o) -> o ]>
    | tm_ex  T => Some <[ (T -> o) -> o ]>
    end.

  Theorem type_check_sound c t T :
    type_check c t = Some T -> has_type c t T.
  Proof.
    generalize dependent c.
    generalize dependent T.
    induction t; intros T c TC;
      try (simpl in TC; injection TC; intros <-; constructor).
    - now constructor.
    - remember (type_check c t1) as T1.
      remember (type_check c t2) as T2.
      simpl in TC. rewrite <- HeqT1, <- HeqT2 in TC.
      destruct T1, T2; try discriminate.
      remember (is_ty_arr t0) as it.
      destruct it eqn : E; try discriminate.
      destruct p. symmetry in Heqit.
      apply ty_arr_is_ty_arr in Heqit.
      destruct (eqb_ty t4 t3) eqn : E1; [|discriminate].
      apply eqb_ty_eq in E1.
      injection TC. intros. subst.
      eapply t_app.
      + apply IHt1. symmetry. eassumption.
      + apply IHt2. now symmetry.
    - simpl in TC.
      remember (type_check (c ++ [t0]) t1) as H.
      destruct H; try discriminate.
      injection TC. intros <-.
      constructor. apply IHt. now symmetry.
  Qed.

  Theorem type_check_complete c t T :
    has_type c t T -> type_check c t = Some T.
  Proof.
    generalize dependent c.
    generalize dependent T.
    induction t; intros T c TC;
    inversion TC; subst; try reflexivity; simpl.
    - assumption.
    - erewrite IHt1, IHt2; try eassumption.
      rewrite is_ty_arr_ty_arr.
      destruct (eqb_ty_spec A A);
        [reflexivity|contradiction].
    - erewrite IHt; [|eassumption]. reflexivity.
  Qed.

  Theorem type_check_has_type c t T :
    has_type c t T <-> type_check c t = Some T.
  Proof.
    split; intros H.
    - now apply type_check_complete.
    - now apply type_check_sound.
  Qed.

  Theorem has_type_unique c t A B :
    has_type c t A -> has_type c t B -> A = B.
  Proof.
    repeat rewrite type_check_has_type.
    intros HA HB. rewrite HA in HB. now injection HB.
  Qed.

  Notation "<| gam |- t : T |>" := (has_type gam t T)
    (at level 0, gam custom stlc_ty at level 200,
    t custom stlc_tm, T custom stlc_ty) : stlc_scope.

  Theorem has_type_length c (n : nat) T :
    has_type c n T -> n < length c.
  Proof.
    intros HT. inversion HT. apply nth_error_Some.
    match goal with | H : _ |- _ => rewrite H end.
    discriminate.
  Qed.


  (********************)
  (** ** Substitution *)
  (********************)

  Fixpoint change_bound m (t : tm) f : tm :=
    match t with
      | tm_lvl n => tm_lvl (if Nat.leb m n then f n else n)
      | tm_app t1 t2 => tm_app (change_bound m t1 f) (change_bound m t2 f)
      | tm_abs T t1 => tm_abs T (change_bound m t1 f)
      | const => const
    end.

  Theorem change_bound_comp m t f g :
    (forall x, m <= x -> f x >= m) ->
    change_bound m (change_bound m t f) g =
    change_bound m t (fun x => g (f x)).
  Proof.
    intros F. induction t; try reflexivity.
    - simpl. destruct (leb_spec m n).
      + destruct (leb_spec m (f n)); [reflexivity|].
        apply F in H. lia.
      + destruct (leb_spec m n); [|reflexivity]. lia.
    - simpl. now rewrite IHt1, IHt2.
    - simpl. now rewrite IHt.
  Qed.

  Theorem change_bound_id m t f :
    (forall x, f x = x) -> change_bound m t f = t.
  Proof.
    intros H. induction t; try reflexivity.
    - simpl. destruct (leb_spec m n); auto.
    - simpl. now rewrite IHt1, IHt2.
    - simpl. now rewrite IHt.
  Qed.

  (** Increase the bound levels in a term by 1 *)
  Definition incr_bound m t := change_bound m t S.

  Fixpoint subst m (l : list tm) (t : tm) : tm :=
    match t with
    | tm_lvl n => nth n l n
    | tm_app s t => tm_app (subst m l s) (subst m l t)
    | tm_abs T t =>
        tm_abs T (subst (m+1) ((map (incr_bound m) l) ++ [tm_lvl m]) t)
    | const => const
    end.

  (** Examples *)
  Compute fun i => subst 1 [<{ \: i, 1 }>; tm_lvl 0] <{ \: o, 1 0 }>.
  Compute fun i => subst 2 [<{ \: i, 1 }>; tm_lvl 0] <{ \: o, 1 0 }>.
  Compute fun i => subst 2 [<{ \: i, 0 1 }>] <{ \: o, 0 }>.
  Compute fun i => subst 1 [<{ \: i, 0 1 }>] <{ \: o, 0 }>.
  Compute fun i => subst 0 [<{ \: i, 0 0 }>] <{ \: o, 0 }>.
  Compute fun i => subst 4 [tm_lvl 0; <{ \: i, 5 }>; tm_lvl 2] <{ 1 2 }>.
  Compute fun i => subst 2 [tm_lvl 0; <{ \: i, 1 2 }>] <{ \: o, 1 }>.
  Compute fun i =>
    subst 0 [tm_lvl 0; tm_lvl 1; <{ \: i, 0 0 }>] <{ \: o, \: i, 2 2 }>.
  Compute subst 0 [ tm_top ] <{ \: o, 1 }>.

  Compute incr_bound 3 <{ \: o, \: o, 0 1 2 }>.

  Definition C := [ty_prp; ty_prp].
  Definition t := <{ \: o, \: o, 0 }>.
  Compute type_check C t.
  Compute type_check (C ++ [ty_prp]) (incr_bound (length C) t).

  Fixpoint contains t n :=
    match t with
    | tm_lvl m => Nat.eqb m n
    | tm_abs T s => contains s n
    | tm_app s1 s2 => orb (contains s1 n) (contains s2 n)
    | _ => false
    end.

  Theorem contains_has_type C D c d t T :
    contains t (length C) = false ->
    has_type (C ++ [c] ++ D) t T ->
    has_type (C ++ [d] ++ D) t T.
  Proof.
    generalize dependent T.
    generalize dependent D.
    induction t; intros D T HC HT;
      inversion HT; subst; econstructor; simpl in *.
    - destruct (ltb_spec n (length C)).
      + rewrite nth_error_app1 in *; assumption.
      + assert (E : forall x, C ++ x :: D = (C ++ [x]) ++ D);
          [intros; now rewrite <- app_assoc|].
        rewrite E in *.
        apply eqb_neq in HC.
        rewrite nth_error_app2 in *; rewrite length_app in *;
          simpl in *; try assumption; lia.
    - eapply IHt1; [|eassumption].
      destruct (contains t1 (length C)); [|reflexivity].
      rewrite orb_true_l in HC. discriminate.
    - eapply IHt2; [|eassumption].
      destruct (contains t2 (length C)); [|reflexivity].
      rewrite orb_true_r in HC. discriminate.
    - rewrite <- app_assoc in *.
      eapply IHt; eassumption.
  Qed.

  Theorem has_type_incr_bound1 C D c t T :
    has_type (C ++ D) t T ->
    has_type ((C ++ [c]) ++ D) (incr_bound (length C) t) T.
  Proof.
    generalize dependent T.
    generalize dependent D.
    induction t; intros D T HT;
      inversion HT; subst; econstructor; simpl in *.
    - destruct (leb_spec (length C) n).
      + rewrite nth_error_app2; rewrite length_app;
          [|simpl; lia].
        rewrite nth_error_app2 in H1; [|assumption].
        rewrite <- H1. f_equal.
        replace (length [c]) with 1; [|reflexivity]. lia.
      + rewrite <- app_assoc.
        rewrite nth_error_app1 in *; assumption.
    - apply IHt1; eassumption.
    - apply IHt2; assumption.
    - rewrite <- app_assoc. apply IHt.
      now rewrite app_assoc.
  Qed.

  Theorem has_type_incr_bound2 C D c t T :
    has_type ((C ++ [c]) ++ D)
      (incr_bound (length C) t) T ->
    has_type (C ++ D) t T.
  Proof.
    generalize dependent T.
    generalize dependent D.
    induction t; intros D T HT;
      inversion HT; subst; econstructor; simpl in *.
    - destruct (leb_spec (length C) n).
      + rewrite nth_error_app2 in *;
        try rewrite length_app in *; try (simpl; lia).
        replace (S n - (_ + _)) with (n - length C) in H1;
          [assumption|].
        replace (length [c]) with 1; [|reflexivity]. lia.
      + rewrite <- app_assoc in *.
        rewrite nth_error_app1 in *; assumption.
    - apply IHt1; eassumption.
    - apply IHt2; assumption.
    - rewrite <- app_assoc. apply IHt.
      now rewrite app_assoc.
  Qed.

  Theorem has_type_switch C c d t T :
    has_type (C ++ [c; d])
      (incr_bound (length C + 1) t) T ->
    has_type (C ++ [d; c]) (incr_bound (length C) t) T.
  Proof.
    intros HT.
    replace (C ++ [d; c]) with ((C ++ [d]) ++ [c]);
      [|now rewrite <- app_assoc].
    apply has_type_incr_bound1.
    replace (C ++ [c; d]) with (((C ++ [c]) ++ [d]) ++ []) in HT;
      [|rewrite app_nil_r; now rewrite <- app_assoc].
    replace (length C + 1) with (length (C ++ [c])) in HT;
      [|apply length_app].
    apply has_type_incr_bound2 in HT.
    now rewrite app_nil_r in HT.
  Qed.

  Theorem has_type_app C c t T : has_type C t T ->
    has_type (C ++ [c]) (incr_bound (length C) t) T.
  Proof.
    intros HT.
    generalize dependent T.
    generalize dependent C.
    induction t; simpl; intros C T HT;
      inversion HT; subst; try constructor.
    - rewrite <- H1.
      destruct (PeanoNat.Nat.leb_spec0 (length C) n).
      + generalize nth_error_None. intros N.
        edestruct N as [_ N1]. rewrite N1.
        * symmetry. now apply N.
        * rewrite length_app. simpl. lia.
      + apply PeanoNat.Nat.nle_gt in n0.
        now rewrite nth_error_app1.
    - eapply t_app.
      + apply IHt1. eassumption.
      + now apply IHt2.
    - apply IHt in H3.
      rewrite <- app_assoc in *. simpl in *.
      apply has_type_switch.
      rewrite length_app in H3. apply H3.
  Qed.

  Theorem has_type_subst1 C T S t s :
    Forall2 (fun si Si => has_type C si Si) s S ->
    has_type S t T ->
    has_type C (subst (length C) s t) T.
  Proof.
    generalize dependent s. generalize dependent S.
    generalize dependent T. generalize dependent C.
    induction t; simpl; intros C T S s F HT;
      inversion HT; subst; try constructor.
    - generalize dependent s.
      generalize dependent n.
      induction S; intros n HT Hn s F.
      + simpl in *. inversion HT. subst.
        rewrite nth_error_nil in *. discriminate.
      + destruct s.
        * apply Forall2_length in F. discriminate.
        * inversion F. subst.
          destruct n as [|n].
          -- simpl in *. injection Hn. intros. now subst.
          -- simpl in *.
             destruct (ltb_spec n (length s)).
             ++ rewrite nth_indep with (d' := tm_lvl n);
                  [|assumption].
                apply IHS; try assumption.
                constructor. inversion HT. subst.
                assumption.
             ++ generalize nth_error_None.
                intros N. edestruct N.
                rewrite H1 in Hn; [discriminate|].
                apply Forall2_length in H4.
                now rewrite <- H4.
    - econstructor.
      + eapply IHt1; eassumption.
      + eapply IHt2; eassumption.
    - replace (length C + 1) with (length (C ++ [t0]));
        [|apply length_app].
      eapply IHt; [|eassumption].
      apply Forall2_app.
      + clear IHt HT H3.
        generalize dependent s.
        induction S; intros s F.
        * destruct s; [constructor|].
          apply Forall2_length in F. discriminate.
        * destruct s.
          -- apply Forall2_length in F. discriminate.
          -- inversion F. subst.
             constructor; [now apply has_type_app|].
             now apply IHS.
      + constructor; constructor.
        rewrite nth_error_app2; [|lia].
        now rewrite sub_diag.
  Qed.

  Theorem has_type_subst2 C T S t s :
    length C <= length S ->
    Forall2 (fun si Si => has_type C si Si) s S ->
    has_type C (subst (length C) s t) T ->
    has_type S t T.
  Proof.
    generalize dependent s. generalize dependent S.
    generalize dependent T. generalize dependent C.
    induction t; simpl; intros C T S s L F HT;
      try solve [inversion HT; constructor].
    - assert (exists A, has_type S n A). {
        destruct (ltb_spec n (length S)).
        - apply nth_error_Some in H.
          destruct (nth_error S n) eqn : E.
          + exists t0. now constructor.
          + exfalso. now apply H.
        - apply Forall2_length in F.
          rewrite nth_overflow in HT; [|now rewrite F].
          inversion HT. subst.
          generalize nth_error_None as N.
          intros N. edestruct N.
          rewrite H1 in H2; [discriminate|]. lia.
      }
      destruct H. replace T with x; [assumption|].
      eapply has_type_subst1 in H; [|eassumption].
      simpl in H.
      eapply has_type_unique; eassumption.
    - inversion HT. subst. econstructor.
      + eapply IHt1; eassumption.
      + eapply IHt2; eassumption.
    - inversion HT. subst. constructor.
      eapply (IHt (C ++ [t0])).
      3:{
        replace (length C + 1) with (length (C ++ [t0]));
          [|apply length_app].
        rewrite length_app. simpl. apply H3.
      }
      + repeat rewrite length_app. simpl. lia.
      + apply Forall2_app.
        * clear IHt HT H3 B t1 L.
          generalize dependent s.
          induction S; intros s F.
          -- destruct s; [constructor|].
             apply Forall2_length in F. discriminate.
          -- destruct s.
             ++ apply Forall2_length in F. discriminate.
             ++ inversion F. subst.
                constructor; [now apply has_type_app|].
                apply IHS; assumption.
        * constructor; constructor.
          rewrite nth_error_app2; [|lia].
          now rewrite sub_diag.
  Qed.
End Stlc.
