From Coq Require Import List.
Import ListNotations.


(***********************************)
(** * Simply Typed Lambda Calculus *)
(***********************************)


(**************)
(** ** Syntax *)
(**************)


(** *** Types *)

Inductive ty : Set :=
  | ty_proposition : ty
  | ty_individual : ty
  | ty_arrow : ty -> ty -> ty.

(** Notations *)

Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.
Declare Custom Entry stlc_ty.

Notation "<[ x ]>" := x (x custom stlc_ty) : stlc_scope.
Notation "x" := x (in custom stlc_ty at level 0, x global) : stlc_scope.
Notation "( t )" := t
  (in custom stlc_ty at level 0, t custom stlc_ty) : stlc_scope.
Notation "A -> B" := (ty_arrow A B)
  (in custom stlc_ty at level 99, right associativity) : stlc_scope.
Notation "'o'" := ty_proposition (in custom stlc_ty at level 0) : stlc_scope.
Notation "'i'" := ty_individual (in custom stlc_ty at level 0) : stlc_scope.

(** Examples *)
Check <[ o ]>.
Check <[ o -> i ]>.
Check <[ o -> (i -> o) ]>.
Check <[ (o -> i) -> o ]>.


(** *** Terms *)

(** Terms using de Bruijn levels *)
Inductive tm : Set :=
  | tm_level : nat -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : ty -> tm -> tm.

(** Notations *)

Declare Custom Entry stlc_tm.

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
Coercion tm_level : nat >-> tm.

(** Examples *)
Check <{ \: i, 1 }>.
Check <{ \: (i -> i), 1 }>.
Check <{ (\: (i -> i), 2) 1 }>.


(**************)
(** ** Typing *)
(**************)

Inductive has_type : list ty -> tm -> ty -> Prop :=
  | T_Var : forall gam x T, nth_error gam x = Some T -> has_type gam x T
  | T_Abs : forall gam T1 T2 t1,
      has_type (gam ++ [T2]) t1 T1 ->
      has_type gam <{ \: T2, t1 }> <[ T2 -> T1 ]>
  | T_App : forall T1 T2 gam t1 t2,
      has_type gam t1 <[ T2 -> T1 ]> ->
      has_type gam t2 T2 ->
      has_type gam <{ t1 t2 }> T1.

(** Notations *)

Infix "++" := app
  (in custom stlc_ty at level 60, right associativity) : stlc_scope.
Infix "::" := cons (in custom stlc_ty at level 60, right associativity) : stlc_scope.
Notation "[ ]" := nil (in custom stlc_ty, format "[ ]") : stlc_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..))
  (in custom stlc_ty,
  format "[ '[' x ;  '/' y ;  '/' .. ;  '/' z ']' ]") : stlc_scope.

Notation "<| gam |- t : T |>" := (has_type gam t T)
  (at level 0, gam custom stlc_ty at level 200,
  t custom stlc_tm, T custom stlc_ty) : stlc_scope.
(*Notation "<| |- t : T |>" := (has_type nil t T)
  (at level 0, t custom stlc_tm, T custom stlc_ty) : stlc_scope.*)

(** Examples *)

Theorem ex1 : <| [i; o] |- 0 : i |>.
Proof. now apply T_Var. Qed.

Theorem ex2 : <| [i; o] |- 1 : o |>.
Proof. now apply T_Var. Qed.

Theorem ex3 : <| [] |- \: i -> o, \: i, 0 1 : (i -> o) -> i -> o |>.
Proof.
  apply T_Abs. simpl. apply T_Abs. simpl.
  eapply T_App.
  - apply T_Var. simpl. reflexivity.
  - apply T_Var. simpl. reflexivity.
Qed.


(********************)
(** ** Substitution *)
(********************)

(** Increase the levels in a term by 1 *)
Fixpoint incr (t : tm) : tm :=
  match t with
  | tm_level n => tm_level (S n)
  | tm_app t1 t2 => tm_app (incr t1) (incr t2)
  | tm_abs T t1 => tm_abs T (incr t1)
  end.

Reserved Notation "[ x := s ] t"
  (in custom stlc_tm at level 5, x constr, s custom stlc_tm,
  t custom stlc_tm at next level, right associativity).
Fixpoint subst (x : nat) (s : tm) (t : tm) : tm :=
  match t with
  | tm_level n => if Nat.eqb n x then s else t
  | <{ t1 t2 }> => <{ [x:=s]t1 [x:=s]t2 }>
  | <{ \: T, t1 }> => <{ \: T, [x := $(incr s)] t1 }>
  end
where "[ x := s ] t" := (subst x s t) (in custom stlc_tm) : stlc_scope.

(** Examples *)
Compute <{ [1 := (\: i, 5)] (1 2) }>.
Compute <{ [1 := (\: i, 1 2)] (\: o, 1) }>.
Compute <{ [2 := (\: i, 0 0)] (\: o, \: i, 2 2) }>.
