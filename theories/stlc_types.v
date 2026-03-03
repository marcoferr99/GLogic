From stdpp Require Export decidable.
Require Export rlist.


(*********************************************)
(** * Types for Simply Typed Lambda Calculus *)
(*********************************************)


(** ** Interface *)

Declare Custom Entry stlc_ty.

(** Interface for the types of stlc.  There must be a type for propositions and
    an arrow type. *)
Module Type TY.
  Parameter ty : Set.
  Parameter ty_prp : ty.
  Parameter ty_arr : ty -> ty -> ty.
  Parameter ty_other : ty -> Prop.

  (*
  Declare Instance eq_ty_dec : EqDecision ty.
  *)

  Parameter ty_rect :
    forall P : ty -> Type,
    P ty_prp ->
    (forall t, P t -> forall s, P s -> P (ty_arr t s)) ->
    (forall t, ty_other t -> P t) ->
    forall t, P t.

  Axiom ty_rect_prp : forall P p a d, ty_rect P p a d ty_prp = p.
  Axiom ty_rect_arr : forall P p a d A B,
     ty_rect P p a d (ty_arr A B) = a _ (ty_rect P p a d A) _ (ty_rect P p a d B).
  Axiom ty_rect_other : forall P p a d t,
    forall O : ty_other t, ty_rect P p a d t = d t O.
End TY.

Module TyChurch <: TY.
  Inductive tyc : Set :=
    | tyc_prp : tyc
    | tyc_arr : tyc -> tyc -> tyc
    | tyc_obj : tyc.

  Definition ty := tyc.
  Definition ty_prp := tyc_prp.
  Definition ty_arr := tyc_arr.

  Definition ty_other t : Prop :=
    match t with
    | tyc_prp => False
    | tyc_arr _ _ => False
    | _ => True
    end.

  (*
  Instance eq_ty_dec : EqDecision ty.
  Proof. solve_decision. Defined.
  *)

  Definition ty_rect :
    forall P : ty -> Type,
    P ty_prp ->
    (forall t, P t -> forall s, P s -> P (ty_arr t s)) ->
    (forall t, ty_other t -> P t) ->
    forall t, P t :=
    fun P p a (o : forall t, ty_other t -> P t) => tyc_rect P p a (o tyc_obj I).

  Theorem ty_rect_prp P p a d : ty_rect P p a d ty_prp = p.
  Proof. reflexivity. Qed.

  Theorem ty_rect_arr P p a d A B :
    ty_rect P p a d (ty_arr A B) =
    a _ (ty_rect P p a d A) _ (ty_rect P p a d B).
  Proof. reflexivity. Qed.

  Theorem ty_rect_other P p a d t :
    forall O : ty_other t, ty_rect P p a d t = d t O.
  Proof.
    intros. destruct t; simpl; destruct O. reflexivity.
  Qed.
End TyChurch.


(** ** Theories *)

Module TyTheories (Ty : TY) (Rlist : RLIST).
  Export Ty.
  Module RlistTheories := RlistTheories Rlist.
  Export RlistTheories.


  (** Notations *)
  Notation "-[ x ]-" := x (x custom stlc_ty) : stlc_scope.
  Notation "x" := x (in custom stlc_ty at level 0, x global) : stlc_scope.
  Notation "A -> B" := (ty_arr A B)
    (in custom stlc_ty at level 99, right associativity) : stlc_scope.
  Notation "( t )" := t
    (in custom stlc_ty at level 0, t custom stlc_ty) : stlc_scope.
  Notation "'o'" := ty_prp (in custom stlc_ty at level 0) : stlc_scope.

  (** Tactics *)
  Create HintDb ty.
  Hint Rewrite ty_rect_prp ty_rect_arr : ty.
  Hint Rewrite ty_rect_other using assumption : ty.
  Ltac ty_simpl := repeat (simpl in *; autorewrite with ty in *).


  (*
  Definition ty_match {T : Set} p a d : ty -> T :=
    ty_rec (fun _ => T) p (fun A _ B _ => a A B) (fun _ => d).
    *)

  Definition ty_rec (P : ty -> Set) := ty_rect P.
  Definition ty_ind (P : ty -> Prop) := ty_rect P.

  Inductive tyv : Set :=
    | tyv_prp : tyv
    | tyv_arr : tyv -> tyv -> tyv
    | tyv_other : ty -> tyv.

  Definition to_tyv : ty -> tyv :=
    ty_rec _
      tyv_prp
      (fun _ fA _ fB => tyv_arr fA fB)
      (fun T _ => tyv_other T).

  Fixpoint to_ty T : ty :=
    match T with
    | tyv_prp => ty_prp
    | tyv_arr A B => ty_arr (to_ty A) (to_ty B)
    | tyv_other T => T
    end.

  Theorem to_tyv_arr A B : to_tyv (ty_arr A B) = tyv_arr (to_tyv A) (to_tyv B).
  Proof. unfold to_tyv. now ty_simpl. Qed.

  Theorem to_ty_to_tyv T : to_ty (to_tyv T) = T.
  Proof.
    induction T using ty_ind; unfold to_tyv, ty_rec in *; ty_simpl; congruence.
  Qed.

  Hint Rewrite to_tyv_arr to_ty_to_tyv : ty.


  Theorem ty_arr_inj A B C D :
    ty_arr A B = ty_arr C D -> A = C /\ B = D.
  Proof.
    intros H.
    apply (f_equal to_tyv) in H. ty_simpl.
    injection H. intros H1 H2.
    apply (f_equal to_ty) in H1, H2. ty_simpl.
    now split.
  Qed.


  Definition context := rlist ty.
End TyTheories.


(** ** Church Implementation *)

Module TyChurchTheories.
  Module TyTheories := TyTheories TyChurch RlistList.
  Import TyTheories.

  Notation "'i'" := tyc_obj (in custom stlc_ty at level 0) : stlc_scope.

  (** Examples *)
  Check -[ o ]-.
  Check -[ o -> i ]-.
  Check -[ o -> (i -> o) ]-.
  Check -[ (o -> i) -> o ]-.
End TyChurchTheories.
