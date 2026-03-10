Require Export stlc.


Module GStlc <: STLC.
  Declare Module Ty : TY.
  Module TyTheories := TyTheories Ty.
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

  Definition type_check_other t :=
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


  Fixpoint nom_map (f : ty -> nat -> nat) t : tm :=
    match t with
    | gtm_nom T a => gtm_nom T (f T a)
    | gtm_abs T t => tm_abs T (nom_map f t)
    | gtm_app s t => tm_app (nom_map f s) (nom_map f t)
    | x => x
    end.

  Inductive invertible {A B} (f : A -> B) : Prop :=
    invertible_intro g :
      (forall x, f (g x) = x) ->
      (forall x, g (f x) = x) ->
      invertible f.

  Theorem has_type_nom_map f C T t :
    has_type C t T <-> has_type C (nom_map f t) T.
  Proof.
    revert C T.
    induction t; intros C T; tm_simpl; try easy.
    - split; intros [A]; exists A; now first [apply IHt1|apply IHt2].
    - split; intros [B]; exists B; now try apply IHt.
    - split; intros H; inversion H; subst; now tm_simpl.
  Qed.

  Inductive tm_equiv m : tm -> tm -> Prop :=
    tm_equiv_intro a b f :
      (forall T, invertible (f T)) -> lambda_equiv m a (nom_map f b) ->
      tm_equiv m a b.

  Theorem has_type_tm_equiv (C : context) T a b : tm_equiv C a b ->
    has_type C a T -> has_type C b T.
  Proof.
    intros TE HT. induction TE.
    eapply has_type_nom_map.
    eapply has_type_lambda_equiv; eassumption.
  Qed.

  Inductive in_supp : tm -> tm -> Prop :=
    | is_nom T n : in_supp (gtm_nom T n) (gtm_nom T n)
    | is_appL a b n : in_supp a n -> in_supp (gtm_app a b) n
    | is_appR a b n : in_supp b n -> in_supp (gtm_app a b) n
    | is_abs T t n : in_supp t n -> in_supp (gtm_abs T t) n.

  Theorem in_supp_other b t : in_supp b t -> tm_other t.
  Proof. intros H. induction H; easy. Qed.
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
