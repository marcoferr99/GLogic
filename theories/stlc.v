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
  | tm_lvl : nat -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : ty -> tm -> tm
  | tm_bot : tm
  | tm_top : tm
  | tm_and : tm
  | tm_or  : tm
  | tm_imp : tm
  | tm_for : ty -> tm.

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
Check <{ \: i, 0 }>.
Check <{ (\: (i -> o), 2) 1 }>.
Check <{ \: o, 3 _| }>.


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
      has_type gam <{ t1 t2 }> T1
  | T_Bot gam : has_type gam tm_bot ty_proposition
  | T_Top gam : has_type gam tm_top ty_proposition
  | T_And gam :
      has_type gam tm_and <[ o -> o -> o ]>
  | T_Or gam :
      has_type gam tm_or <[ o -> o -> o ]>
  | T_Imp gam :
      has_type gam tm_imp <[ o -> o -> o ]>
  | T_For gam T :
      has_type gam (tm_for T) <[ (T -> o) -> o ]>.

(** Notations *)

Infix "++" := app
  (in custom stlc_ty at level 60, right associativity) : stlc_scope.
Infix "::" := cons (in custom stlc_ty at level 60, right associativity) : stlc_scope.
Notation "[ ]" := nil (in custom stlc_ty, format "[ ]") : stlc_scope.
Notation "[ x ]" := (cons x nil) (in custom stlc_ty) : stlc_scope.
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

Theorem ex4 : <| [] |- \: i, _| : i -> o |>.
Proof.  apply T_Abs. simpl. apply T_Bot. Qed.

Theorem ex5 : forall T, ~ <| [] |- \: i, 1 : T |>.
Proof.
  intros T P.
  inversion P. simpl in *. subst.
  inversion H3. simpl in *. subst. discriminate.
Qed.


(********************)
(** ** Substitution *)
(********************)

Notation "[ x ]" := (cons x nil) (in custom stlc_tm) : stlc_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..))
  (in custom stlc_tm,
  format "[ '[' x ;  '/' y ;  '/' .. ;  '/' z ']' ]") : stlc_scope.

(** Increase the levels in a term by 1 *)
Fixpoint incr m (t : tm) : tm :=
  match t with
  | tm_lvl n => tm_lvl (if Nat.leb m n then S n else n)
  | tm_app t1 t2 => tm_app (incr m t1) (incr m t2)
  | tm_abs T t1 => tm_abs T (incr m t1)
  | x => x
  end.

Reserved Notation "[ l | m ] t"
  (in custom stlc_tm at level 5, l custom stlc_tm at level 0,
  t custom stlc_tm at next level, right associativity).
Fixpoint subst (m : nat) (l : list tm) (t : tm) : tm :=
  match t with
  | tm_lvl n => nth n l n
  | <{ t1 t2 }> => <{ [l|m]t1 [l|m]t2 }>
  | <{ \: T, t1 }> => <{ \: T, [$(map (incr m) l) | m] t1 }>
  | x => x
  end
where "[ l | m ] t" := (subst m l t) (in custom stlc_tm) : stlc_scope.

(** Examples *)
Compute <{ [[\: i, 1; $(tm_lvl 0)] | 1] \: o, 1 0 }>.
Compute <{ [[\: i, 1; $(tm_lvl 0)] | 2] \: o, 1 0 }>.
Compute <{ [[\: i, 0 1] | 2] \: o, 0 }>.
Compute <{ [[\: i, 0 1] | 1] \: o, 0 }>.
Compute <{ [[\: i, 0 0] | 0] \: o, 0 }>.

Compute <{ [[$(tm_lvl 0); \: i, 5; $(tm_lvl 2)] | 4] (1 2) }>.
Compute <{ [[$(tm_lvl 0); \: i, 1 2] | 2] (\: o, 1) }>.
Compute <{ [[$(tm_lvl 0); $(tm_lvl 1); \: i, 0 0] | 0] (\: o, \: i, 2 2) }>.
