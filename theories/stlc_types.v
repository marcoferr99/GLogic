Require Export tactics rlist.
From Ltac2 Require Export Rewrite.


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

  Instance ty_inhabited : Inhabited ty := populate ty_prp.

  Definition ty_rec (P : ty -> Set) := ty_rect P.
  Definition ty_ind (P : ty -> Prop) := ty_rect P.


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
  (*
  Ltac2 mutable ty_lemmas () :=
    List.map (fun x => Strategy.term x true) [preterm:(ty_rect_prp); preterm:(ty_rect_arr)].
  Ltac2 Notation ty_simpl :=
    rewrite_strat (Strategy.topdown (Strategy.choices (ty_lemmas ()))) None; simpl.
    *)
  Ltac2 ty_simpl c := autorewrite @ty c; s_simpl c.
  Ltac2 Notation "ty_simpl" "in" h(ident) := ty_simpl (one_hyp h).
  Ltac2 Notation "ty_simpl" := ty_simpl goal.
  (* Tactic Notation "ty_simpl" "in" "*" := repeat (simpl in *; autorewrite with ty in * ).  *)
  Ltac2 Notation "ty_induction" h(constr) := induction $h using ty_rect.


  (** *** View *)

  Module ty_view.
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
    Proof.
      unfold to_tyv. now ty_simpl.
    Qed.

    Theorem to_tyv_other T : ty_other T ->
      to_tyv T = tyv_other T.
    Proof.
      intros. unfold to_tyv. now ty_simpl.
    Qed.


    Fixpoint to_ty T : ty :=
      match T with
      | tyv_prp => ty_prp
      | tyv_arr A B => ty_arr (to_ty A) (to_ty B)
      | tyv_other T => T
      end.

    Theorem to_ty_to_tyv T : to_ty (to_tyv T) = T.
    Proof.
      ty_induction T.
      - now rewrite to_tyv_prp.
      - rewrite to_tyv_arr. simpl. congruence.
      - now rewrite to_tyv_other.
    Qed.
  End ty_view.


  (** *** Injection and discriminate *)

  Theorem ty_arr_inj {X Y A B} : ty_arr X Y = ty_arr A B -> X = A /\ Y = B.
  Proof.
    intros H.
    apply (f_equal ty_view.to_tyv) in H. repeat (rewrite ty_view.to_tyv_arr in H).
    injection H. intros HY HX.
    apply (f_equal ty_view.to_ty) in HY. apply (f_equal ty_view.to_ty) in HX.
    repeat (rewrite ty_view.to_ty_to_tyv in *). auto.
  Qed.

  Ltac2 Notation "ty_injection" h(ident) :=
    Control.enter (fun () =>
      let c := Control.hyp h in c_injection [fun () => 'ty_arr_inj] c
    ).

  (*
  Ltac2 ty_lemmas () :=
    List.map (fun x => Strategy.term x true) [preterm:(ty_rect_prp); preterm:(ty_rect_arr)].
  Ltac2 ty_simpl1 h :=
    rewrite_strat (Strategy.topdown (Strategy.choices (ty_lemmas ()))) (Some h).
  *)

  Ltac2 ty_discriminate_f x :=
    lazy_match! x with
    | ty_prp => '(ty_rect (fun _ => Prop) True (fun _ _ _ _ => False) (fun _ _ => False))
    | ty_arr _ _ => '(ty_rect (fun _ => Prop) False (fun _ _ _ _ => True) (fun _ _ => False))
    | _ => '(ty_rect (fun _ => Prop) False (fun _ _ _ _ => False) (fun _ _ => True))
    end.

  Ltac2 ty_discriminate_rew h :=
    repeat (first [
      rewrite ty_rect_prp in $h
    | rewrite ty_rect_arr in $h
    | rewrite ty_rect_other in $h by assumption
    ]).

  Ltac2 Notation "ty_discriminate" h(ident) :=
    c_discriminate ty_discriminate_f (ty_discriminate_rew) h.


  (** *** Other *)

  Instance ty_eq_dec : EqDecision ty.
  Proof.
    intros x.
    ty_induction x; destruct y using ty_rec;
      try (right; intros N; ty_discriminate N).
    - now constructor.
    - destruct (IHx1 y1), (IHx2 y2); subst; try (now left);
        right; intros N; ty_injection N; congruence.
    - now apply ty_eq_dec_other.
  Qed.


  Definition context := rlist ty.
End TyTheories.
