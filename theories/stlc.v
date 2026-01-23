From Coq Require Export List.
Export ListNotations.


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

  Definition ty := tyc.
  Definition ty_prp := tyc_prp.
  Definition ty_arr := tyc_arr.
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
    | tm_abs T t => tm_abs T (subst m (map (incr_bound m) l) t)
    | const => const
    end.

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
      apply IHt.

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
