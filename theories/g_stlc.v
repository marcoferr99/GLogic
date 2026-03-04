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

  Theorem tm_other_lvl : forall n, ~ tm_other (tm_lvl n).
  Proof. intros n N. inversion N. Qed.

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

  Inductive ghas_type : context -> gtm -> ty -> Prop :=
    | t_lvl c n T : c !! n = Some T -> ghas_type c (gtm_lvl n) T
    | t_app c A B s t : ghas_type c s (ty_arr A B) -> ghas_type c t A ->
        ghas_type c (gtm_app s t) B
    | t_abs c A B t : ghas_type (c +: A) t B ->
        ghas_type c (gtm_abs A t) (ty_arr A B)
    | t_bot c : ghas_type c gtm_bot ty_prp
    | t_top c : ghas_type c gtm_top ty_prp
    | t_and c : ghas_type c gtm_and -[ o -> o -> o ]-
    | t_or  c : ghas_type c gtm_or  -[ o -> o -> o ]-
    | t_imp c : ghas_type c gtm_imp -[ o -> o -> o ]-
    | t_for c T : ghas_type c (gtm_for T) -[ (T -> o) -> o ]-
    | t_ex  c T : ghas_type c (gtm_ex  T) -[ (T -> o) -> o ]-
    | t_nab c T : ghas_type c (gtm_nab T) -[ (T -> o) -> o ]-
    | t_nom c T n : ghas_type c (gtm_nom T n) T.

  Definition has_type := ghas_type.

  Theorem has_type_lvl : forall c n T,
    has_type c (tm_lvl n) T <-> c !! n = Some T.
  Proof.
    split; intros.
    - now inversion H.
    - now constructor.
  Qed.

  Theorem has_type_app : forall c s t B,
    has_type c (tm_app s t) B <->
    exists A, has_type c s (ty_arr A B) /\  has_type c t A.
  Proof.
    split; intros.
    - inversion H. eauto.
    - destruct H as [? [? ?]]. econstructor; eassumption.
  Qed.

  Theorem has_type_abs : forall c A T t,
    has_type c (tm_abs A t) T <->
    exists B, has_type (c +: A) t B /\ T = -[ A -> B ]-.
  Proof.
    split; intros.
    - inversion H. subst. exists B. now split.
    - destruct H as [? [? ?]]. subst. now constructor.
  Qed.

  Theorem has_type_other_indep : forall c d t T,
    tm_other t -> has_type c t T -> has_type d t T.
  Proof.
    intros c d t T O Ht.
    destruct t; try (inversion Ht; constructor); exfalso; destruct O.
  Qed.

  Theorem has_type_other_unique : forall c t A B,
    tm_other t -> has_type c t A -> has_type c t B -> A = B.
  Proof.
    intros c t A B Ot HA HB.
    destruct t; inversion HA; inversion HB; now subst.
  Qed.
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
  Notation "'for' T , t" := (tm_app (gtm_for T) (tm_abs T t))
    (in custom stlc_tm at level 200, T custom stlc_ty,
      t custom stlc_tm at level 200, left associativity) : stlc_scope.
  Notation "'ex' T , t" := (tm_app (gtm_ex T) (tm_abs T t))
    (in custom stlc_tm at level 200, T custom stlc_ty,
      t custom stlc_tm at level 200, left associativity) : stlc_scope.
  Notation "'nab' T , t" := (tm_app (gtm_nab T) (tm_abs T t))
    (in custom stlc_tm at level 200, T custom stlc_ty,
      t custom stlc_tm at level 200, left associativity) : stlc_scope.


  Record permut : Set := {
    permutf : nat -> nat;
    permutb : nat -> nat;
    _ : forall n, permutf (permutb n) = n;
    _ : forall n, permutb (permutf n) = n;
  }.

  (*
  Definition equiv m t s : Prop :=
    exists p : permut, lambda_equiv m t (permutf p s).
    *)
  Parameter tm_equiv : nat -> tm -> tm -> Prop.
  Parameter supp : tm -> list tm.
  Parameter type_check : context -> tm -> ty.
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
