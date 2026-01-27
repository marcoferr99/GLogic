From stdpp Require Import decidable list.


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

  Declare Instance eq_ty_dec : EqDecision ty.

  Parameter ty_rec :
    forall P : ty -> Set,
    P ty_prp ->
    (forall t, P t -> forall s, P s -> P (ty_arr t s)) ->
    (forall t, P t) ->
    forall t, P t.

  Parameter ty_ind :
    forall P : ty -> Prop,
    P ty_prp ->
    (forall t, P t -> forall s, P s -> P (ty_arr t s)) ->
    (forall t, t <> ty_prp -> (forall A B, t <> ty_arr A B) -> P t) ->
    forall t, P t.

  Axiom ty_rec_prp : forall P p a d, ty_rec P p a d ty_prp = p.
  Axiom ty_rec_arr : forall P p a d A B,
    ty_rec P p a d (ty_arr A B) = a _ (ty_rec P p a d A) _ (ty_rec P p a d B).
  Axiom ty_rec_neq : forall P p a d t,
    t <> ty_prp -> (forall A B, t <> ty_arr A B) -> ty_rec P p a d t = d t.
End TY.

(** Global notation declarations. *)
Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.
Declare Custom Entry stlc_ty.

Module TyTheories (Ty : TY).
  Export Ty.

  Definition context := list ty.

  Notation "-[ x ]-" := x (x custom stlc_ty) : stlc_scope.
  Notation "x" := x (in custom stlc_ty at level 0, x global) : stlc_scope.
  Notation "A -> B" := (ty_arr A B)
    (in custom stlc_ty at level 99, right associativity) : stlc_scope.
  Notation "( t )" := t
    (in custom stlc_ty at level 0, t custom stlc_ty) : stlc_scope.
  Notation "'o'" := ty_prp (in custom stlc_ty at level 0) : stlc_scope.

  Notation "l +: e" := (l ++ [e]) (at level 60) : stlc_scope.

  Create HintDb ty.
  Hint Rewrite ty_rec_prp ty_rec_arr : ty.
  Ltac tysimpl := simpl in *; autorewrite with ty in *.
End TyTheories.

Module TyChurch <: TY.
  Inductive tyc : Set :=
    | tyc_prp : tyc
    | tyc_arr : tyc -> tyc -> tyc
    | tyc_obj : tyc.

  Definition ty := tyc.
  Definition ty_prp := tyc_prp.
  Definition ty_arr := tyc_arr.

  Instance eq_ty_dec : EqDecision ty.
  Proof. solve_decision. Defined.

  Definition ty_rec :
    forall P : ty -> Set,
    P ty_prp ->
    (forall t, P t -> forall s, P s -> P (ty_arr t s)) ->
    (forall t, P t) ->
    forall t, P t :=
    fun P p a d => tyc_rec P p a (d tyc_obj).

  Theorem ty_ind :
    forall P : ty -> Prop,
    P ty_prp ->
    (forall t, P t -> forall s, P s -> P (ty_arr t s)) ->
    (forall t, t <> ty_prp ->
      (forall A B, t <> ty_arr A B) -> P t) ->
    forall t, P t.
  Proof. induction t; auto. Qed.

  Theorem ty_rec_prp P p a d : ty_rec P p a d ty_prp = p.
  Proof. reflexivity. Qed.

  Theorem ty_rec_arr P p a d A B :
    ty_rec P p a d (ty_arr A B) =
    a _ (ty_rec P p a d A) _ (ty_rec P p a d B).
  Proof. reflexivity. Qed.

  Theorem ty_rec_neq P p a d t :
    t <> ty_prp -> (forall A B, t <> ty_arr A B) ->
    ty_rec P p a d t = d t.
  Proof.
    intros Np Na. destruct t as [|x y|].
    - contradiction.
    - exfalso. now apply (Na x y).
    - reflexivity.
  Qed.
End TyChurch.

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


  (**************)
  (** ** Typing *)
  (**************)

  Inductive has_type : context -> tm -> ty -> Prop :=
    | t_lvl c n T : c !! n = Some T -> has_type c (tm_lvl n) T
    | t_abs c A B t : has_type (c +: A) t B ->
        has_type c (tm_abs A t) (ty_arr A B)
    | t_app c A B s t : has_type c s (ty_arr A B) -> has_type c t A ->
        has_type c (tm_app s t) B
    | t_bot c : has_type c tm_bot ty_prp
    | t_top c : has_type c tm_top ty_prp
    | t_and c : has_type c tm_and -[ o -> o -> o ]-
    | t_or  c : has_type c tm_or  -[ o -> o -> o ]-
    | t_imp c : has_type c tm_imp -[ o -> o -> o ]-
    | t_for c T : has_type c (tm_for T) -[ (T -> o) -> o ]-
    | t_ex  c T : has_type c (tm_ex  T) -[ (T -> o) -> o ]-.

  Fixpoint type_check (c : context) (t : tm) : option ty :=
    match t with
    | tm_lvl n => c !! n
    | tm_abs A t =>
        match type_check (c +: A) t with
        | Some B => Some -[ A -> B ]-
        | _ => None
        end
    | tm_app s t =>
        match type_check c s, type_check c t with
        | Some AR, Some A1 =>
            ty_rec _ None (fun A _ B _ =>
            if decide (A = A1) then Some B else None) (fun t => None) AR
        | _, _ => None
        end
    | tm_bot => Some ty_prp
    | tm_top => Some ty_prp
    | tm_and => Some -[ o -> o -> o ]-
    | tm_or  => Some -[ o -> o -> o ]-
    | tm_imp => Some -[ o -> o -> o ]-
    | tm_for T => Some -[ (T -> o) -> o ]-
    | tm_ex  T => Some -[ (T -> o) -> o ]-
    end.

  Notation "<| gam |- t : T |>" := (has_type gam t T)
    (at level 0, gam custom stlc_ty at level 200,
    t custom stlc_tm, T custom stlc_ty) : stlc_scope.

  Theorem type_check_sound c t T :
    type_check c t = Some T -> has_type c t T.
  Proof.
    generalize dependent c. generalize dependent T.
    induction t as [| s IHs t IHt | s t | | | | | | |];
    intros T c TC; try (simpl in TC; injection TC;
      intros <-; constructor).
    - now constructor.
    - simpl in TC.
      destruct (type_check c s) as [A|] eqn : Es;
        [|discriminate].
      destruct (type_check c t) as [B|] eqn : Et;
        [|discriminate].
      destruct A as [|X _ Y _ |] using ty_ind;
        tysimpl; try discriminate.
      + destruct (decide (X = B)); [|discriminate].
        injection TC. intros <-. subst.
        econstructor; eauto.
      + rewrite ty_rec_neq in TC; try assumption.
        discriminate.
    - simpl in TC.
      destruct (type_check (c +: s) t) eqn : E;
        try discriminate.
      injection TC. intros <-. constructor.
      now apply IHt.
  Qed.

  Theorem type_check_complete c t T :
    has_type c t T -> type_check c t = Some T.
  Proof.
    generalize dependent c.
    generalize dependent T.
    induction t as [| s IHs t IHt | s t | | | | | | |];
      intros T c TC;
      inversion TC; subst; try reflexivity; simpl.
    - assumption.
    - erewrite IHs, IHt; try eassumption.
      tysimpl. destruct (decide (A = A));
        [reflexivity|contradiction].
    - erewrite IHt; [reflexivity|eassumption].
  Qed.

  Theorem type_check_has_type c t T :
    has_type c t T <-> type_check c t = Some T.
  Proof.
    split; intros.
    - now apply type_check_complete.
    - now apply type_check_sound.
  Qed.

  Theorem has_type_unique c t A B :
    has_type c t A -> has_type c t B -> A = B.
  Proof.
    repeat rewrite type_check_has_type.
    intros -> H. now injection H.
  Qed.

  Theorem has_type_length c (n : nat) T :
    has_type c n T -> n < length c.
  Proof.
    intros HT. inversion HT. subst.
    eapply lookup_lt_Some. eassumption.
  Qed.


  (********************)
  (** ** Substitution *)
  (********************)

  Fixpoint change_bound f m (t : tm) : tm :=
    match t with
      | tm_lvl n => tm_lvl (if decide (m <= n) then f n else n)
      | tm_app s t => tm_app (change_bound f m s) (change_bound f m t)
      | tm_abs T t => tm_abs T (change_bound f m t)
      | const => const
    end.

  Theorem change_bound_comp f g m t :
    (forall x, m <= x -> m <= f x) ->
    change_bound g m (change_bound f m t) =
    change_bound (fun x => g (f x)) m t.
  Proof.
    intros F.
    induction t; try reflexivity; simpl; try now f_equal.
    destruct (decide (m <= n)).
    - destruct (decide (m <= f n)); [reflexivity|].
      exfalso. auto.
    - destruct (decide (m <= n));
      [contradiction|reflexivity].
  Qed.

  Theorem change_bound_id f m t :
    (forall x, f x = x) -> change_bound f m t = t.
  Proof.
    intros.
    induction t; try reflexivity; simpl; try now f_equal.
    destruct (decide (m <= n)); auto.
  Qed.

  (** Increase the bound levels in a term by 1 *)
  Definition incr_bound := change_bound S.

  Fixpoint subst m (l : list tm) (t : tm) : tm :=
    match t with
    | tm_lvl n => nth n l n
    | tm_app s t => tm_app (subst m l s) (subst m l t)
    | tm_abs T t =>
        tm_abs T (subst (m+1) ((incr_bound m <$> l) +: tm_lvl m) t)
    | const => const
    end.


  Theorem has_type_incr_bound1 C D c t T :
    has_type (C ++ D) t T ->
    has_type (C +: c ++ D) (incr_bound (length C) t) T.
  Proof.
    generalize dependent T.
    generalize dependent D.
    induction t; intros D T HT;
      inversion HT; subst; econstructor; simpl in *.
    - destruct (decide (length C <= n)).
      + rewrite @lookup_app_r in *; try assumption;
          rewrite length_app; [|simpl; lia].
        match goal with [H : _ |- _] => rewrite <- H end.
        f_equal. simpl. lia.
      + rewrite <- app_assoc.
        rewrite (lookup_app_l C) in *; try assumption; lia.
    - eauto.
    - eauto.
    - rewrite <- app_assoc.
      match goal with [H : _ |- _] => apply H end.
      now rewrite app_assoc.
  Qed.

  Theorem has_type_incr_bound2 C D c t T :
    has_type (C +: c ++ D) (incr_bound (length C) t) T ->
    has_type (C ++ D) t T.
  Proof.
    generalize dependent T.
    generalize dependent D.
    induction t; intros D T HT;
      inversion HT; subst; econstructor; simpl in *.
    - destruct (decide (length C <= n)).
      + rewrite @lookup_app_r in *; try assumption;
        rewrite length_app in *; [|simpl; lia].
        match goal with [H : _ |- _] => rewrite <- H end.
        f_equal. simpl. lia.
      + rewrite <- app_assoc in *.
        rewrite @lookup_app_l in *; try assumption; lia.
    - eauto.
    - eauto.
    - rewrite <- app_assoc.
      match goal with [H : _ |- _] => apply H end.
      now rewrite app_assoc.
  Qed.

  Theorem has_type_switch C c d t T :
    has_type (C +: c +: d)
      (incr_bound (length (C +: c)) t) T ->
    has_type (C +: d +: c) (incr_bound (length C) t) T.
  Proof.
    intros HT.
    apply has_type_incr_bound1.
    rewrite <- (app_nil_r (C +: c)).
    rewrite <- (app_nil_r ((C +: c) +: d)) in HT.
    eapply has_type_incr_bound2.
    eassumption.
  Qed.

  Theorem has_type_app C c t T : has_type C t T ->
    has_type (C +: c) (incr_bound (length C) t) T.
  Proof.
    intros HT.
    generalize dependent T. generalize dependent C.
    induction t; simpl; intros C T HT;
      inversion HT; subst; try constructor.
    - destruct (decide (length C <= n)).
      + rewrite @lookup_ge_None_2 in H1;
          [discriminate|assumption].
      + now apply lookup_app_l_Some.
    - eapply t_app; eauto.
    - apply has_type_switch. auto.
  Qed.

  Theorem has_type_subst1 C T S t s :
    Forall2 (fun si Si => has_type C si Si) s S ->
    has_type S t T ->
    has_type C (subst (length C) s t) T.
  Proof.
    generalize dependent s. generalize dependent S.
    generalize dependent T. generalize dependent C.
    induction t as [| |c ? IH| | | | | | |];
    simpl; intros C T S s F HT;
      inversion HT; subst; try constructor.
    - generalize dependent s. generalize dependent n.
      induction S as [|h t IH]; intros n HT Hn s F;
        [now rewrite @lookup_nil in Hn|].
      destruct s;
        [apply Forall2_length in F; discriminate|].
      inversion F. subst.
      destruct n as [|n]; simpl in *;
        [injection Hn; intros; now subst|].
      destruct (Nat.ltb_spec n (length s)).
      + rewrite nth_indep with (d' := tm_lvl n);
          [|assumption].
        apply IH; try assumption.
        constructor. inversion HT. now subst.
      + rewrite lookup_ge_None_2 in Hn; [discriminate|].
        replace (length t) with (length s); [assumption|].
        eapply Forall2_length. eassumption.
    - econstructor; eauto.
    - replace (length C + 1) with (length (C +: c));
        [|apply length_app].
      eapply IH; [|eassumption].
      apply Forall2_app.
      + clear dependent B. generalize dependent s.
        induction S; intros s F; destruct s;
          try (apply Forall2_length in F; discriminate);
          [constructor|].
          inversion F. subst.
          constructor; [now apply has_type_app|].
          now apply IHS.
      + constructor; constructor.
        rewrite @lookup_app_r; [|auto].
        now rewrite Nat.sub_diag.
  Qed.

  Theorem has_type_subst2 C T S t s :
    length C <= length S ->
    Forall2 (fun si Si => has_type C si Si) s S ->
    has_type C (subst (length C) s t) T ->
    has_type S t T.
  Proof.
    generalize dependent s. generalize dependent S.
    generalize dependent T. generalize dependent C.
    induction t; simpl; intros C T S s L F HT;
      try solve [inversion HT; constructor].
    - assert (exists A, has_type S n A). {
        destruct (Nat.ltb_spec n (length S)).
        - apply lookup_lt_is_Some_2 in H.
          destruct H as [X H].
          exists X. now constructor.
        - apply Forall2_length in F.
          rewrite nth_overflow in HT; [|now rewrite F].
          inversion HT. subst.
          rewrite @lookup_ge_None_2 in H2;
            [discriminate|lia].
      }
      destruct H as [X H]. replace T with X; [assumption|].
      eapply has_type_subst1 in H; [|eassumption].
      simpl in H. eapply has_type_unique; eassumption.
    - inversion HT. subst. econstructor; eauto.
    - inversion HT. subst. constructor.
      eapply (IHt (C +: t)).
      3:{
        replace (length C + 1) with (length (C +: t));
          [|apply length_app].
        rewrite length_app. simpl. apply H3.
      }
      + repeat rewrite length_app. simpl. lia.
      + apply Forall2_app.
        -- clear dependent B L. generalize dependent s.
           induction S; intros s F; destruct s;
           try (apply Forall2_length in F; discriminate);
           [constructor|].
           inversion F. subst.
           constructor;
             [now apply has_type_app|now apply IHS].
        -- constructor; constructor.
           rewrite @lookup_app_r; [|lia].
           now rewrite Nat.sub_diag.
  Qed.
End Stlc.


(****************)
(** ** Examples *)
(****************)

Module StlcChurch.
  Module Stlc := Stlc TyChurch.
  Import Stlc.
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
End StlcChurch.
