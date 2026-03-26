Require Export stlc_types.


(** * Church Implementation *)

Module TyChurch : TY.
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

  Definition ty_eq_dec_other A B :
    ty_other A -> ty_other B -> Decision (A = B).
  Proof. solve_decision. Qed.
End TyChurch.


(*
Module TyChurchTheories.
  Module TyTheories := TyTheories TyChurch.
  Import TyTheories.

  Notation "'i'" := tyc_obj (in custom stlc_ty at level 0) : stlc_scope.

  (** Examples *)
  Check -[ o ]-.
  Check -[ o -> i ]-.
  Check -[ o -> (i -> o) ]-.
  Check -[ (o -> i) -> o ]-.
End TyChurchTheories.
*)
