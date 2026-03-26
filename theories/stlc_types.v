Require Export base rlist.


(*********************************************)
(** * Types for Simply Typed Lambda Calculus *)
(*********************************************)


(** ** Interface *)

(** Interface for the types of stlc.  There must be a type for propositions and
    an arrow type. *)
Module Type TY.
  Parameter ty : Set.
  Parameter ty_prp : ty.
  Parameter ty_arr : ty -> ty -> ty.
  Parameter ty_other : ty -> Prop.

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

  Parameter ty_eq_dec_other :
    forall A B, ty_other A -> ty_other B -> Decision (A = B).
End TY.


(** ** Theories *)

Declare Custom Entry stlc_ty.

Module TyTheories (Ty : TY).
  Export Ty.

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
  Tactic Notation "ty_simpl" := repeat (simpl; autorewrite with ty).
  Tactic Notation "ty_simpl" "in" ident(H) := repeat (simpl in H; autorewrite with ty in H).
  Tactic Notation "ty_simpl" "in" "*" := repeat (simpl in *; autorewrite with ty in *).


  Instance ty_inhabited : Inhabited ty := populate ty_prp.

  Definition ty_rec (P : ty -> Set) := ty_rect P.
  Definition ty_ind (P : ty -> Prop) := ty_rect P.

  Theorem ty_other_prp : ~ ty_other ty_prp.
  Proof.
    intros N.
    set (f := ty_rect _ false (fun _ _ _ _ => false) (fun _ _ => true)).
    assert (E : f ty_prp = f ty_prp) by reflexivity. subst f.
    rewrite ty_rect_prp in E at 1.
    now rewrite ty_rect_other in E.
  Qed.

  Theorem ty_other_arr A B : ~ ty_other (ty_arr A B).
  Proof.
    intros N.
    set (f := ty_rect _ false (fun _ _ _ _ => false) (fun _ _ => true)).
    assert (E : f (ty_arr A B) = f (ty_arr A B)) by reflexivity. subst f.
    rewrite ty_rect_arr in E at 1.
    now rewrite ty_rect_other in E.
  Qed.

  Inductive tyv : Set :=
    | tyv_prp : tyv
    | tyv_arr : tyv -> tyv -> tyv
    | tyv_other : ty -> tyv.

  Definition to_tyv : ty -> tyv :=
    ty_rec _
      tyv_prp
      (fun _ fA _ fB => tyv_arr fA fB)
      (fun T _ => tyv_other T).

  Theorem to_tyv_prp : to_tyv ty_prp = tyv_prp.
  Proof. unfold to_tyv. now ty_simpl. Qed.

  Theorem to_tyv_arr A B :
    to_tyv (ty_arr A B) = tyv_arr (to_tyv A) (to_tyv B).
  Proof. unfold to_tyv. now ty_simpl. Qed.

  Hint Rewrite to_tyv_prp to_tyv_arr : ty.


  Fixpoint to_ty T : ty :=
    match T with
    | tyv_prp => ty_prp
    | tyv_arr A B => ty_arr (to_ty A) (to_ty B)
    | tyv_other T => T
    end.

  Theorem to_ty_to_tyv T : to_ty (to_tyv T) = T.
  Proof.
    induction T using ty_ind; unfold to_tyv; ty_simpl; congruence.
  Qed.

  Hint Rewrite to_ty_to_tyv : ty.


  Ltac to_tyv H := apply (f_equal to_tyv) in H; ty_simpl in H.
  Ltac to_ty H :=
    match type of H with
    | to_tyv ?x = _ => apply (f_equal to_ty) in H; repeat rewrite to_ty_to_tyv in H
    end.
  Tactic Notation "to_ty" := match goal with [H : _ |- _] => to_ty H end.
  Ltac ty_injection H := to_tyv H; injection H; intros; repeat to_ty; subst; clear H.
  Ltac ty_discriminate H :=
    match type of H with
    | ty_other ty_prp => exfalso; now apply ty_other_prp
    | ty_other (ty_arr ?A ?B) => exfalso; now apply (ty_other_arr A B)
    | _ => to_tyv H; discriminate H
    end.
  Tactic Notation "ty_discriminate" ident(H) := ty_discriminate H.
  Tactic Notation "ty_discriminate" :=
    match goal with | [H : _ |- _] => ty_discriminate H end.
  Ltac ty_induction T := induction T using ty_rect.


  Instance ty_eq_dec : EqDecision ty.
  Proof.
    intros x. ty_induction x; destruct y using ty_rec;
      try (right; intros N; subst; ty_discriminate).
    - now constructor.
    - destruct (IHx1 y1), (IHx2 y2); subst; try (now left);
        right; intros N; now ty_injection N.
    - now apply ty_eq_dec_other.
  Qed.


  Definition context := rlist ty.
End TyTheories.
