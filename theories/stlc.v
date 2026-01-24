From Coq Require Export List.
Export ListNotations.
Require Import Lia.


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

  Parameter eqb_ty : ty -> ty -> bool.
  Axiom eqb_ty_eq : forall A B, eqb_ty A B = true -> A = B.
  Parameter is_ty_arr : ty -> option (ty * ty).
  Axiom is_ty_arr_ty_arr : forall A B, is_ty_arr (ty_arr A B) = Some (A, B).
  Axiom ty_arr_is_ty_arr :
    forall A B t, is_ty_arr t = Some (A, B) -> t = ty_arr A B.
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
  Check tyc_rec.

  Definition ty := tyc.
  Definition ty_prp := tyc_prp.
  Definition ty_arr := tyc_arr.

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
            match is_ty_arr AR with
            | Some (A, B) => if eqb_ty A A1 then Some B else None
            | _ => None
            end
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
      remember (is_ty_arr t) as it.
      destruct it eqn : E; try discriminate.
      destruct p. symmetry in Heqit.
      apply ty_arr_is_ty_arr in Heqit.
      destruct (eqb_ty t3 t0) eqn : E1; [|discriminate].
      apply eqb_ty_eq in E1.
      injection TC. intros. subst.
      eapply t_app.
      + apply IHt1. symmetry. eassumption.
      + apply IHt2. now symmetry.
    - simpl in TC.
      remember (type_check (c ++ [t]) t0) as H.
      destruct H; try discriminate.
      injection TC. intros <-.
      constructor. apply IHt. now symmetry.
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

  (** Increase the bound levels in a term by 1 *)
  Fixpoint incr_bound m (t : tm) : tm :=
    match t with
    | tm_lvl n => tm_lvl (if Nat.leb m n then S n else n)
    | tm_app t1 t2 => tm_app (incr_bound m t1) (incr_bound m t2)
    | tm_abs T t1 => tm_abs T (incr_bound m t1)
    | const => const
    end.

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

  Theorem th C c t T : has_type C t T ->
    has_type (C ++ [c]) (incr_bound (length C) t) T.
  Proof.
    intros HT.
    generalize dependent T.
    induction t; simpl; intros T HT.
    - constructor. inversion HT. subst. rewrite <- H1.
      destruct (PeanoNat.Nat.leb_spec0 (length C) n).
      + generalize nth_error_None. intros N.
        edestruct N as [_ N1]. rewrite N1.
        * symmetry. now apply N.
        * rewrite length_app. simpl. lia.
      + apply PeanoNat.Nat.nle_gt in n0.
        now rewrite nth_error_app1.
    - inversion HT. subst. eapply t_app.
      + apply IHt1. eassumption.
      + now apply IHt2.
    - inversion HT. subst.
      constructor.

    intros HT.
    induction HT; simpl.
    - constructor. rewrite <- H.
      destruct (PeanoNat.Nat.leb_spec0 (length c0) n).
      + generalize nth_error_None. intros N.
        edestruct N as [_ N1]. rewrite N1.
        * symmetry. now apply N.
        * rewrite length_app. simpl. lia.
      + apply PeanoNat.Nat.nle_gt in n0.
        now rewrite nth_error_app1.
    - constructor.


  Theorem has_type_subst C S T t s :
    Forall (fun si => has_type C si (S si)) s ->
    has_type (map S s) t T ->
    has_type C (subst (length C) s t) T.
  Proof.
    intros F HT.
    generalize dependent s. generalize dependent T.
    generalize dependent C.
    induction t; simpl; intros C T s F HT.
    - inversion HT. subst.
      eapply nth_error_nth in H1. rewrite map_nth in H1.
      eapply Forall_nth in F.
      + rewrite H1 in F. apply F.
      + erewrite <- length_map.
        eapply has_type_length. eassumption.
    - inversion HT. subst. eapply t_app.
      + apply IHt1; eassumption.
      + auto.
    - inversion HT. subst. constructor.
      replace (length C + 1) with (length (C ++ [t])).
      apply IHt.
      + apply Forall_app. split.
        * Print Forall.


  Theorem subst_lemma (A : ty) (t : tm) (s : list tm) (T : list ty) (S : tm -> ty) :
    Forall (fun si => <| T |- si : $(S si) |>) s -> (
        <| $(map S s) |- t : A |> <-> <| T |- [s | length T] t : A |>
    ).
  Proof.
    intros F. split; intros H.
    - generalize dependent A. induction t; intros A H.
      + simpl.
      + simpl. eapply T_App.
        * apply IHt1.
        Search Forall nth.
        induction s.
        * simpl in *. inversion H. subst.
          rewrite nth_error_nil in H2. discriminate.
        * simpl in *.
End Stlc.


  Theorem th C t T n m : has_type C t T ->
    n >= length C -> m >= length C ->
    incr_bound n t = incr_bound m t.
  Proof.
    intros HT.
    generalize dependent m. generalize dependent n.
    induction HT; simpl; intros a b Ha Hb.
    - assert (n < length c). {
        generalize nth_error_None. intros N. edestruct N.
        destruct (PeanoNat.Nat.leb_spec0 (length c) n).
        - now rewrite H1 in H.
        - lia.
      }
      destruct (PeanoNat.Nat.leb_spec0 a n), (PeanoNat.Nat.leb_spec0 b n); try reflexivity; lia.
    - erewrite IHHT.
      + reflexivity.
      +

