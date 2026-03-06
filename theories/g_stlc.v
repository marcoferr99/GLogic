Require Export stlc.


Module GStlc <: STLC.
  Declare Module Ty : TY.
  Declare Module Rlist : RLIST.
  Module TyTheories := TyTheories Ty Rlist.
  Export TyTheories.

  Inductive gtm : Set :=
    | gtm_lvl : nat -> gtm
    | gtm_app : gtm -> gtm -> gtm
    | gtm_abs : ty -> gtm -> gtm
    | gtm_bot : gtm
    | gtm_top : gtm
    | gtm_and : gtm
    | gtm_or  : gtm
    | gtm_imp : gtm
    | gtm_for : ty -> gtm
    | gtm_ex  : ty -> gtm
    | gtm_nab : ty -> gtm
    | gtm_nom : ty -> nat -> gtm.

  Definition tm := gtm.
  Definition tm_lvl := gtm_lvl.
  Definition tm_app := gtm_app.
  Definition tm_abs := gtm_abs.

  Definition tm_other t : Prop :=
    match t with
    | gtm_lvl _ => False
    | gtm_app _ _ => False
    | gtm_abs _ _ => False
    | _ => True
    end.

  Definition tm_rect (P : gtm -> Type) l a b (o : forall t (O : tm_other t), P t) : forall t, P t :=
    gtm_rect P l a b (o gtm_bot I) (o gtm_top I) (o gtm_and I) (o gtm_or I) (o gtm_imp I) (fun t => o (gtm_for t) I) (fun t => o (gtm_ex t) I) (fun t => o (gtm_nab t) I) (fun t n => o (gtm_nom t n) I).

  Theorem tm_rect_lvl : forall P l a b o n, tm_rect P l a b o (tm_lvl n) = l n.
  Proof. reflexivity. Qed.

  Theorem tm_rect_app : forall P l a b o s t,
    tm_rect P l a b o (tm_app s t) = a _ (tm_rect P l a b o s) _ (tm_rect P l a b o t).
  Proof. reflexivity. Qed.

  Theorem tm_rect_abs : forall P l a b o T t,
    tm_rect P l a b o (tm_abs T t) = b T _ (tm_rect P l a b o t).
  Proof. reflexivity. Qed.

  Theorem tm_rect_other : forall t P l a b o,
    forall O : tm_other t, tm_rect P l a b o t = o t O.
  Proof.
    intros t **.
    destruct t; simpl; destruct O; reflexivity.
  Qed.

  Definition has_type_other t :=
    match t with
    | gtm_bot => ty_prp
    | gtm_top => ty_prp
    | gtm_for T => -[ (T -> o) -> o ]-
    | gtm_ex  T => -[ (T -> o) -> o ]-
    | gtm_nab T => -[ (T -> o) -> o ]-
    | gtm_and => -[ o -> o -> o ]-
    | gtm_or  => -[ o -> o -> o ]-
    | gtm_imp => -[ o -> o -> o ]-
    | gtm_nom T n => T
    | _ => ty_prp
    end.
End GStlc.

Module GStlcTheories.
  Module StlcTheories := StlcTheories GStlc.
  Export StlcTheories.

  (** Notations *)
  Notation "<{ x }>" := x (x custom stlc_tm at level 200) : stlc_scope.
  Notation "x" := x
    (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
  Notation "( t )" := t
    (in custom stlc_tm at level 0, t custom stlc_tm) : stlc_scope.
  Notation "$( x )" := x
    (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
  Notation "x \/ y" := (tm_app (tm_app gtm_or x) y)
    (in custom stlc_tm at level 60, left associativity) : stlc_scope.
  Notation "x /\ y" := (tm_app (tm_app gtm_and x) y)
    (in custom stlc_tm at level 50, left associativity) : stlc_scope.
  Notation "x > y" := (tm_app (tm_app gtm_imp x) y)
    (in custom stlc_tm at level 70, left associativity) : stlc_scope.
  Notation "'for' T , t" := (tm_app (gtm_for T) (tm_abs T t))
    (in custom stlc_tm at level 200, T custom stlc_ty,
      t custom stlc_tm at level 200, left associativity) : stlc_scope.
  Notation "'ex' T , t" := (tm_app (gtm_ex T) (tm_abs T t))
    (in custom stlc_tm at level 200, T custom stlc_ty,
      t custom stlc_tm at level 200, left associativity) : stlc_scope.
  Notation "'nab' T , t" := (tm_app (gtm_nab T) (tm_abs T t))
    (in custom stlc_tm at level 200, T custom stlc_ty,
      t custom stlc_tm at level 200, left associativity) : stlc_scope.


  (*
  Record permut : Set := {
    permutf : nat -> nat;
    permutb : nat -> nat;
    _ : forall n, permutf (permutb n) = n;
    _ : forall n, permutb (permutf n) = n;
  }.
  *)

  Fixpoint tm_permut (f : ty -> nat -> nat) t : tm :=
    match t with
    | gtm_nom T a => f T a
    | gtm_abs T t => tm_abs T (tm_permut f t)
    | gtm_app s t => tm_app (tm_permut f s) (tm_permut f t)
    | x => x
    end.

  Inductive invertible {A B} (f : A -> B) : Prop :=
    invertible_intro g :
      (forall x, f (g x) = x) ->
      (forall x, g (f x) = x) ->
      invertible f.

  Inductive tm_equiv m : tm -> tm -> Prop :=
    tm_equiv_intro a b f :
      (forall T, invertible (f T)) -> lambda_equiv m a (tm_permut f b) ->
      tm_equiv m a b.

  Parameter supp : tm -> list tm.
End GStlcTheories.


(*
(****************)
(** ** Examples *)
(****************)

Module StlcChurch.
  Module GStlc := GStlc.
  Import GStlc.
  Import TyChurchTheories.

  (** Terms *)
  Check <{ \: i, 0 }>.
  Check <{ (\: (i -> o), 2) 1 }>.
  Check <{ \: o, 3 _| }>.

  (** Typing *)
  Compute type_check [-[ i -> o ]-; tyc_obj] <{ 0 1 }>.

  (** Substitution *)
  Compute subst 1 [<{ \: i, 1 }>; tm_lvl 0] <{ \: o, 1 0 }>.
  Compute subst 2 [<{ \: i, 1 }>; tm_lvl 0] <{ \: o, 1 0 }>.
  Compute subst 2 [<{ \: i, 0 1 }>] <{ \: o, 0 }>.
  Compute subst 1 [<{ \: i, 0 1 }>] <{ \: o, 0 }>.
  Compute subst 0 [<{ \: i, 0 0 }>] <{ \: o, 0 }>.
  Compute subst 4 [tm_lvl 0; <{ \: i, 5 }>; tm_lvl 2] <{ 1 2 }>.
  Compute subst 2 [tm_lvl 0; <{ \: i, 1 2 }>] <{ \: o, 1 }>.
  Compute subst 0 [tm_lvl 0; tm_lvl 1; <{ \: i, 0 0 }>] <{ \: o, \: i, 2 2 }>.
  Compute subst 0 [ tm_top ] <{ \: o, 1 }>.
  Compute subst_last 1 tm_bot <{ \: o, 1 }>.

  (** Reduction *)
  Compute beta_reduction 1 <{ (\: o, 1) 0 }>.
  Compute beta_reduction 0 <{ (\: o -> o, 0) (\: o, 0) }>.
  Compute beta_reduction 0 <{ (\: o -> o, 0) ((\: o -> o, 0) (\: o, 0)) }>.
End StlcChurch.
*)
