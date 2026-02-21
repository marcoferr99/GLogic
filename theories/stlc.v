From stdpp Require Export decidable list.
Import Nat.


(***********************************)
(** * Simply Typed Lambda Calculus *)
(***********************************)


(**************)
(** ** Syntax *)
(**************)

(** Global notation declarations. *)
Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.
Declare Custom Entry stlc_ty.


(** Reverse list interface *)
Module Type RLIST.
  Parameter rlist : Type -> Type.

  Parameter rlength : forall {A}, rlist A -> nat.

  Declare Instance rlist_lookup {A} : Lookup nat A (rlist A).
  Axiom is_Some_lookup : forall {A} (c : rlist A) n,
    is_Some (c !! n) <-> n < rlength c.

  Parameter rcons : forall {A}, rlist A -> A -> rlist A.
  Axiom rlength_rcons :
    forall {A} (c : rlist A) t, rlength (rcons c t) = S (rlength c).
  Axiom lookup_rcons_eq : forall {A} (c : rlist A) t n,
    n = rlength c -> rcons c t !! n = Some t.
  Axiom lookup_rcons_lt : forall {A} (c : rlist A) t n,
    n < rlength c -> rcons c t !! n = c !! n.

  (** Build a list from its length and its (total) lookup function *)
  Parameter build_rlist : forall {A}, nat -> (nat -> A) -> rlist A.
  Axiom rlength_build_rlist : forall {A} n (f : nat -> A),
    rlength (build_rlist n f) = n.
  Axiom lookup_build_rlist : forall {A} l (f : nat -> A) n,
    n < l -> build_rlist l f !! n = Some (f n).

  Declare Instance rlist_fmap : FMap rlist.
  Axiom lookup_fmap : forall {A} {B} (f : A -> B) (l : rlist A) n,
    (f <$> l) !! n = f <$> l !! n.
End RLIST.

Module RlistTheories (Rlist : RLIST).
  Export Rlist.

  Notation "l +: e" := (rcons l e) (at level 50) : stlc_scope.
  Notation "|( c )|" := (rlength c) : stlc_scope.


  Definition lookup_default {A} d n (c : rlist A) : A :=
    match c !! n with
    | None => d
    | Some x => x
    end.

  Theorem lookup_None1 {A} (c : rlist A) n :
    n >= |(c)| -> c !! n = None.
  Proof.
    intros H.
    destruct (c !! n) eqn : E; [|reflexivity].
    assert (n < |(c)|); [|lia].
    apply is_Some_lookup.
    econstructor. eassumption.
  Qed.

  Theorem lookup_None2 {A} (c : rlist A) n :
    c !! n = None -> n >= |(c)|.
  Proof.
    intros H.
    destruct (decide (n < |(c)|)); [|lia].
    apply is_Some_lookup in l. destruct l. now rewrite H in H0.
  Qed.

  Theorem lookup_rcons_gt : forall {A} (c : rlist A) t n,
    n > |(c)| -> rcons c t !! n = None.
  Proof.
    intros. apply lookup_None1.
    rewrite rlength_rcons. lia.
  Qed.

  Inductive lookup_rcons_cases {A} (c : rlist A) t n : Prop :=
    | lookup_rcons_cases_lt (_ : n < |(c)|) (_ : (c +: t) !! n = c !! n)
    | lookup_rcons_cases_eq (_ : n = |(c)|) (_ : (c +: t) !! n = Some t)
    | lookup_rcons_cases_gt (_ : n > |(c)|) (_ : (c +: t) !! n = None).

  Theorem lookup_rcons_spec {A} (c : rlist A) t n : lookup_rcons_cases c t n.
  Proof.
    destruct (lt_total n |(c)|) as [H | [H | H]].
    - apply lookup_rcons_cases_lt; [assumption|].
      now apply lookup_rcons_lt.
    - apply lookup_rcons_cases_eq; [assumption|].
      now apply lookup_rcons_eq.
    - apply lookup_rcons_cases_gt; [assumption|].
      now apply lookup_rcons_gt.
  Qed.

  Ltac lookup_rcons_spec c t n H E :=
    destruct (lookup_rcons_spec c t n) as [H E | H E | H E]; rewrite E in *.

  Theorem is_Some_rlength {A B} (l : rlist A) (h : rlist B) :
    (forall n, is_Some (l !! n) <-> is_Some (h !! n)) ->
    |(l)| = |(h)|.
  Proof.
    intros H. destruct (lt_total |(l)| |(h)|) as [E|[L|G]]; try assumption.
    - apply is_Some_lookup in E. apply H in E.
      apply is_Some_lookup in E. lia.
    - apply is_Some_lookup in G. apply H in G.
      apply is_Some_lookup in G. lia.
  Qed.

  Theorem rlength_fmap : forall {A} {B} (f : A -> B) l,
    |(f <$> l)| = |(l)|.
  Proof.
    intros. apply is_Some_rlength.
    intros. rewrite lookup_fmap. apply fmap_is_Some.
  Qed.
End RlistTheories.


Module RlistList <: RLIST.
  Definition rlist := list.
  Definition rlength := @length.
  Definition rcons {A} l (e : A) := l ++ [e].

  Theorem rlength_rcons {A} :
    forall (c : rlist A) t, length (rcons c t) = S (length c).
  Proof.
    intros. unfold rcons.
    rewrite length_app. simpl. lia.
  Qed.

  Instance rlist_lookup {A} : Lookup nat A (rlist A) := list_lookup.

  Theorem lookup_rcons_lt : forall {A} (c : rlist A) t n,
    n < length c -> rcons c t !! n = c !! n.
  Proof.
    intros. unfold rcons.
    now rewrite @lookup_app_l.
  Qed.

  Theorem is_Some_lookup {A} :
    forall (c : rlist A) n, is_Some (c !! n) <-> n < length c.
  Proof. apply lookup_lt_is_Some. Qed.

  Theorem lookup_rcons_eq : forall {A} (c : rlist A) t n,
    n = length c -> rcons c t !! n = Some t.
  Proof.
    intros. unfold rcons.
    rewrite @lookup_app_r; [|lia].
    subst. now rewrite sub_diag.
  Qed.

  Fixpoint build_rlist {A} n f : rlist A :=
    match n with
    | 0 => []
    | S n => rcons (build_rlist n f) (f n)
    end.

  Theorem rlength_build_rlist : forall {A} n (f : nat -> A),
    length (build_rlist n f) = n.
  Proof.
    intros. induction n; [reflexivity|].
    simpl. unfold rcons.
    rewrite length_app. rewrite IHn. simpl. lia.
  Qed.

  Theorem lookup_build_rlist : forall {A} n (f : nat -> A) x,
    x < n -> build_rlist n f !! x = Some (f x).
  Proof.
    intros. induction n; [lia|].
    simpl. unfold rcons.
    destruct (decide (x = n)).
    - subst. rewrite @lookup_app_r; rewrite rlength_build_rlist; [|lia].
      now rewrite sub_diag.
    - rewrite @lookup_app_l.
      + apply IHn. lia.
      + rewrite rlength_build_rlist. lia.
  Qed.

  Instance rlist_fmap : FMap rlist := list_fmap.

  Theorem lookup_fmap : forall {A} {B} (f : A -> B) (l : rlist A) n,
    (f <$> l) !! n = f <$> l !! n.
  Proof. intros. apply list_lookup_fmap. Qed.
End RlistList.


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

  Axiom ty_rec_prp : forall P p a d, ty_rec P p a d ty_prp = p.
  Axiom ty_rec_arr : forall P p a d A B,
    ty_rec P p a d (ty_arr A B) = a _ (ty_rec P p a d A) _ (ty_rec P p a d B).
  Axiom ty_rec_neq : forall P p a d t,
    t <> ty_prp -> (forall A B, t <> ty_arr A B) -> ty_rec P p a d t = d t.

  Axiom ty_ind :
    forall P : ty -> Prop,
    P ty_prp ->
    (forall t, P t -> forall s, P s -> P (ty_arr t s)) ->
    (forall t, t <> ty_prp -> (forall A B, t <> ty_arr A B) -> P t) ->
    forall t, P t.
End TY.

Module TyTheories (Ty : TY) (Rlist : RLIST).
  Export Ty.
  Module RlistTheories := RlistTheories Rlist.
  Export RlistTheories.

  Notation "-[ x ]-" := x (x custom stlc_ty) : stlc_scope.
  Notation "x" := x (in custom stlc_ty at level 0, x global) : stlc_scope.
  Notation "A -> B" := (ty_arr A B)
    (in custom stlc_ty at level 99, right associativity) : stlc_scope.
  Notation "( t )" := t
    (in custom stlc_ty at level 0, t custom stlc_ty) : stlc_scope.
  Notation "'o'" := ty_prp (in custom stlc_ty at level 0) : stlc_scope.


  Create HintDb ty.
  Hint Rewrite ty_rec_prp ty_rec_arr : ty.
  Ltac ty_simpl := simpl in *; autorewrite with ty in *.


  Definition ty_match {T : Set} p a d : ty -> T :=
    ty_rec (fun _ => T) p (fun A _ B _ => a A B) (fun _ => d).

  Theorem ty_arr_inj A B C D :
    ty_arr A B = ty_arr C D -> A = C /\ B = D.
  Proof.
    intros H. split.
    - apply (f_equal (ty_rec _ ty_prp (fun A _ B _ => A)
        (fun _ => ty_prp))) in H.
      now ty_simpl.
    - apply (f_equal (ty_rec _ ty_prp (fun A _ B _ => B)
        (fun _ => ty_prp))) in H.
      now ty_simpl.
  Qed.


  Definition context := rlist ty.
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
  Proof. intros ? ? ? ? t. induction t; auto. Qed.

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
  Module TyTheories := TyTheories TyChurch RlistList.
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

Module Stlc (Ty : TY) (Rlist : RLIST).
  Module TyTheories := TyTheories Ty Rlist.
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
  Notation "'for' T , t" := (tm_app (tm_for T) (tm_abs T t))
    (in custom stlc_tm at level 200, T custom stlc_ty,
      t custom stlc_tm at level 200, left associativity) : stlc_scope.
  Notation "'ex' T , t" := (tm_app (tm_ex T) (tm_abs T t))
    (in custom stlc_tm at level 200, T custom stlc_ty,
      t custom stlc_tm at level 200, left associativity) : stlc_scope.
  Coercion tm_lvl : nat >-> tm.


  (**************)
  (** ** Typing *)
  (**************)

  Inductive has_type : context -> tm -> ty -> Prop :=
    | t_lvl c n T : c !! n = Some T -> has_type c (tm_lvl n) T
    | t_app c A B s t : has_type c s (ty_arr A B) -> has_type c t A ->
        has_type c (tm_app s t) B
    | t_abs c A B t : has_type (c +: A) t B ->
        has_type c (tm_abs A t) (ty_arr A B)
    | t_bot c : has_type c tm_bot ty_prp
    | t_top c : has_type c tm_top ty_prp
    | t_and c : has_type c tm_and -[ o -> o -> o ]-
    | t_or  c : has_type c tm_or  -[ o -> o -> o ]-
    | t_imp c : has_type c tm_imp -[ o -> o -> o ]-
    | t_for c T : has_type c (tm_for T) -[ (T -> o) -> o ]-
    | t_ex  c T : has_type c (tm_ex  T) -[ (T -> o) -> o ]-.

  Notation "<| gam |- t : T |>" := (has_type gam t T)
    (at level 0, gam custom stlc_ty at level 200,
    t custom stlc_tm, T custom stlc_ty) : stlc_scope.

  Fixpoint type_check (c : context) (t : tm) : option ty :=
    match t with
    | tm_lvl n => c !! n
    | tm_app s t =>
        match type_check c s, type_check c t with
        | Some Ts, Some Tt =>
            (ty_match None
              (fun A B => if decide (A = Tt) then Some B else None) None
            ) Ts
        | _, _ => None
        end
    | tm_abs A t =>
        match type_check (c +: A) t with
        | Some B => Some -[ A -> B ]-
        | _ => None
        end
    | tm_bot => Some ty_prp
    | tm_top => Some ty_prp
    | tm_and => Some -[ o -> o -> o ]-
    | tm_or  => Some -[ o -> o -> o ]-
    | tm_imp => Some -[ o -> o -> o ]-
    | tm_for T => Some -[ (T -> o) -> o ]-
    | tm_ex  T => Some -[ (T -> o) -> o ]-
    end.

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
      unfold ty_match in TC. destruct A as [|X _ Y _ |] using ty_ind;
        ty_simpl; try discriminate.
      + destruct (decide (X = B)); [|discriminate].
        injection TC. intros. subst.
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
      inversion TC; subst; try easy; simpl.
    - erewrite IHs, IHt; try eassumption.
      unfold ty_match. ty_simpl. now destruct (decide (A = A)).
    - now erewrite IHt.
  Qed.

  Theorem type_check_iff c t T :
    has_type c t T <-> type_check c t = Some T.
  Proof.
    split; intros.
    - now apply type_check_complete.
    - now apply type_check_sound.
  Qed.

  Theorem has_type_unique c t A B :
    has_type c t A -> has_type c t B -> A = B.
  Proof.
    repeat rewrite type_check_iff.
    intros -> H. now injection H.
  Qed.


  (***************************)
  (** ** Levels manipulation *)
  (***************************)

  (** Apply "f" to all variables in the term "t" *)
  Fixpoint level_map (f : nat -> nat) (t : tm) : tm :=
    match t with
      | tm_lvl n => tm_lvl (f n)
      | tm_app s t => tm_app (level_map f s) (level_map f t)
      | tm_abs T t => tm_abs T (level_map f t)
      | const => const
    end.

  Theorem level_map_f_eq f g t :
    (forall n, f n = g n) -> level_map f t = level_map g t.
  Proof.
    intros H. induction t; simpl; congruence.
  Qed.

  Definition free_level_map f m :=
    level_map (fun n => if decide (n < m) then f n else n).

  Theorem has_type_free_level_map f c d t T :
    |(c)| = |(d)| -> (forall n, d !! f n = c !! n) ->
    has_type c t T ->
    has_type d (free_level_map f |(c)| t) T.
  Proof.
    generalize dependent T.
    generalize dependent d. generalize dependent c.
    generalize dependent f.
    induction t as [| | t | | | | | | |];
    intros f c d L T F HT; inversion HT; subst;
      unfold free_level_map in *; simpl; try solve [constructor].
    - destruct (decide (n < |(c)|)) as [Hn | Hn].
      + constructor. now rewrite F.
      + exfalso. apply Hn. apply is_Some_lookup.
        econstructor. eassumption.
    - econstructor; eauto.
    - constructor.
      erewrite level_map_f_eq.
      + apply (IHt (fun n => if decide (n < |(c)|) then f n else n));
          try eassumption; [repeat rewrite rlength_rcons; congruence|].
        intros n.
        destruct (decide (n < |(c)|)).
        * repeat rewrite lookup_rcons_lt; try auto.
          apply is_Some_lookup in l. destruct l.
          eapply is_Some_lookup. econstructor.
          rewrite F. eassumption.
        * destruct (decide (n = |(c)|)).
          -- subst. repeat rewrite lookup_rcons_eq; auto.
          -- repeat rewrite lookup_None1; try reflexivity;
               rewrite rlength_rcons; lia.
      + intros n. simpl.
        destruct (decide (n < |(c)|)), (decide (n < |(c +: t)|));
          try reflexivity.
        rewrite rlength_rcons in *. lia.
  Qed.


  (** Apply "f" to all bound variables in the term "t" *)
  Definition bound_level_map f m :=
    level_map (fun n => if decide (m <= n) then f n else n).

  Theorem has_type_bound_level_map_impl1 l m c d t T :
    (l <= |(c)|) ->
    (|(d)| = m + |(c)|) ->
    (forall n, n >= l -> d !! (m + n) = c !! n) ->
    (forall n, n < l -> d !! n = c !! n) ->
    has_type c t T ->
    has_type d (bound_level_map (add m) l t) T.
  Proof.
    generalize dependent T.
    generalize dependent d. generalize dependent c.
    induction t as [| | t | | | | | | |];
    intros c d T Hl L Hlg Hll Hc; inversion Hc; subst;
    unfold bound_level_map in *; simpl; econstructor; try eauto.
    - destruct (decide (l <= n)).
      + now rewrite Hlg.
      + rewrite Hll; [assumption|lia].
    - eapply (IHt (c +: t)); try eassumption; try intros n Hn.
      + rewrite rlength_rcons. lia.
      + repeat rewrite rlength_rcons. lia.
      + lookup_rcons_spec c t n Ic Ec; lookup_rcons_spec d t (m + n) Id Ed;
          try lia; auto.
      + lookup_rcons_spec c t n Ic Ec; lookup_rcons_spec d t n Id Ed;
          try lia; auto.
  Qed.

  Theorem has_type_bound_level_map_impl2 l m c d t T :
    (l <= |(c)|) ->
    (|(d)| = m + |(c)|) ->
    (forall n, n >= l -> d !! (m + n) = c !! n) ->
    (forall n, n < l -> d !! n = c !! n) ->
    has_type d (bound_level_map (add m) l t) T
    ->
    has_type c t T.
  Proof.
    generalize dependent T.
    generalize dependent d. generalize dependent c.
    induction t as [| | t | | | | | | |];
    intros c d T Hl L Hlg Hll Hc; inversion Hc; subst;
    unfold bound_level_map in *; simpl; econstructor; try eauto.
    - destruct (decide (l <= n)).
      + now rewrite <- Hlg.
      + rewrite <- Hll; [assumption|lia].
    - eapply (IHt (c +: t)); try eassumption; try intros n Hn.
      + rewrite rlength_rcons. lia.
      + repeat rewrite rlength_rcons. lia.
      + lookup_rcons_spec c t n Ic Ec; lookup_rcons_spec d t (m + n) Id Ed;
          try lia; auto.
      + lookup_rcons_spec c t n Ic Ec; lookup_rcons_spec d t n Id Ed;
          try lia; auto.
  Qed.

  Theorem has_type_bound_level_map1 m c d t T :
    (|(d)| = m + |(c)|) ->
    (forall n, n < |(c)| -> d !! n = c !! n) ->
    has_type c t T ->
    has_type d (bound_level_map (add m) |(c)| t) T.
  Proof.
    intros. eapply has_type_bound_level_map_impl1; try eassumption; [lia|].
    intros n Hn. repeat rewrite lookup_None1; auto. lia.
  Qed.

  Theorem has_type_bound_level_map_S C c t T :
    has_type C t T ->
    has_type (C +: c) (bound_level_map S |(C)| t) T.
  Proof.
    intros Ht. unfold bound_level_map. erewrite level_map_f_eq.
    - apply (has_type_bound_level_map1 1); try eassumption.
      + rewrite rlength_rcons. lia.
      + intros. rewrite lookup_rcons_lt; easy.
    - intros. reflexivity.
  Qed.

  Theorem has_type_bound_level_map2 m c d t T :
    (|(d)| = m + |(c)|) ->
    (forall n, n < |(c)| -> d !! n = c !! n) ->
    has_type d (bound_level_map (add m) |(c)| t) T ->
    has_type c t T.
  Proof.
    intros. eapply has_type_bound_level_map_impl2; try eassumption; [lia|].
    intros n Hn. repeat rewrite lookup_None1; auto. lia.
  Qed.


  (********************)
  (** ** Substitution *)
  (********************)

  Fixpoint subst m (l : rlist tm) (t : tm) : tm :=
    match t with
    | tm_lvl n => lookup_default (tm_lvl n) n l
    | tm_app s t => tm_app (subst m l s) (subst m l t)
    | tm_abs T t =>
        tm_abs T (subst (S m) ((bound_level_map S m <$> l) +: tm_lvl m) t)
    | const => const
    end.

  Theorem has_type_subst_h n Rn (r : rlist tm) (R C : context) (c : ty) :
    |(r)| = |(R)| ->
    (forall rn, r !! n = Some rn -> R !! n = Some Rn -> has_type C rn Rn) ->
    (forall rn, ((bound_level_map S |( C )| <$> r) +: tm_lvl |( C )|) !! n = Some rn -> (R +: c) !! n = Some Rn -> has_type (C +: c) rn Rn).
  Proof.
    intros L F **.
    destruct (lt_total n |(r)|) as [Ln | [En | Gn]].
    - rewrite lookup_rcons_lt in H; [|now rewrite rlength_fmap].
      rewrite lookup_fmap in H.
      apply fmap_Some in H as (x & Hx1 & Hx2).
      subst rn. apply has_type_bound_level_map_S.
      eapply F; [eassumption|].
      rewrite lookup_rcons_lt in H0; [assumption|].
      now rewrite <- L.
    - rewrite lookup_rcons_eq in H; [|now rewrite rlength_fmap].
      injection H. intros. subst. constructor.
      rewrite <- H0.
      repeat rewrite @lookup_rcons_eq; auto.
    - rewrite lookup_rcons_gt in H; [discriminate|now rewrite rlength_fmap].
  Qed.

  Theorem has_type_subst1 C T R t r :
    |(r)| = |(R)| ->
    (forall n rn Rn, r !! n = Some rn -> R !! n = Some Rn -> has_type C rn Rn) ->
    has_type R t T ->
    has_type C (subst |(C)| r t) T.
  Proof.
    generalize dependent r. generalize dependent R.
    generalize dependent T. generalize dependent C.
    induction t as [| |c ? IH| | | | | | |];
    simpl; intros C T R r L F HT;
      inversion HT; subst; try constructor.
    - unfold lookup_default.
      destruct (r !! n) eqn : E; [now apply (F n) |].
      apply lookup_None2 in E.
      rewrite @lookup_None1 in H1; [discriminate|].
      now rewrite <- L.
    - econstructor; eauto.
    - replace (S |(C)|) with (|(C +: c)|); [|apply rlength_rcons].
      eapply IH; try eassumption.
      + repeat rewrite rlength_rcons. rewrite rlength_fmap.
        now f_equal.
      + intros. eapply has_type_subst_h; eauto.
  Qed.

  Theorem has_type_subst2 C T R t r :
    |(C)| <= |(R)| -> |(r)| = |(R)| ->
    (forall n rn Rn, r !! n = Some rn -> R !! n = Some Rn -> has_type C rn Rn) ->
    has_type C (subst |(C)| r t) T ->
    has_type R t T.
  Proof.
    generalize dependent r. generalize dependent R.
    generalize dependent T. generalize dependent C.
    induction t as [| | t | | | | | | |];
    simpl; intros C T R r L E F HT;
      try solve [inversion HT; constructor].
    - assert (exists A, has_type R n A). {
        destruct (decide (n < |(R)|)) as [Hn | Hn].
        - apply is_Some_lookup in Hn as [x Hx].
          exists x. now constructor.
        - unfold lookup_default in HT.
          rewrite lookup_None1 in HT; [|lia].
          inversion HT. subst.
          rewrite @lookup_None1 in H1; [discriminate|lia].
      }
      destruct H as [X H]. replace T with X; [assumption|].
      eapply has_type_subst1 in H; try eassumption.
      simpl in H. eapply has_type_unique; eassumption.
    - inversion HT. subst. econstructor; eauto.
    - inversion HT. subst. constructor.
      eapply (IHt (C +: t)).
      4:{
        replace (S |(C)|) with (|(C +: t)|) in H3; [|rewrite rlength_rcons; lia].
        apply H3.
      }
      + repeat rewrite rlength_rcons. lia.
      + repeat rewrite rlength_rcons. f_equal.
        now rewrite rlength_fmap.
      + intros. eapply has_type_subst_h; eauto.
  Qed.


  Definition subst_last m s := subst m (build_rlist m tm_lvl +: s).

  Theorem has_type_subst_last C T X s t :
    has_type (C +: T) t X -> has_type C s T ->
    has_type C (subst_last |(C)| s t) X.
  Proof.
    intros Ht Hs.
    eapply has_type_subst1; try eassumption.
    - repeat rewrite rlength_rcons. f_equal.
      apply rlength_build_rlist.
    - intros.
      destruct (lt_total n |(C)|) as [Ln | [En | Gn]].
      + rewrite @lookup_rcons_lt in H, H0; try assumption.
        * rewrite lookup_build_rlist in H; [|assumption].
          injection H. intros <-. now constructor.
        * now rewrite rlength_build_rlist.
      + rewrite @lookup_rcons_eq in H, H0; try assumption.
        * injection H. injection H0. intros <- <-. assumption.
        * now rewrite rlength_build_rlist.
      + rewrite lookup_rcons_gt in H0; [discriminate|lia].
  Qed.


  (*****************)
  (** ** Reduction *)
  (*****************)

  Fixpoint level_prop P t : bool :=
    match t with
    | tm_lvl m => P m
    | tm_abs T s => level_prop P s
    | tm_app s1 s2 => orb (level_prop P s1) (level_prop P s2)
    | _ => false
    end.

  Definition contains_bound_levels m n :=
    level_prop (fun x => andb (leb m x) (ltb x (n + m))).

  Theorem bound_level_map_id m n t :
    contains_bound_levels m n t = false ->
    bound_level_map (add n) m (bound_level_map (fun x => x - n) m t) = t.
  Proof.
    unfold bound_level_map, contains_bound_levels. intros L.
    induction t; try reflexivity; simpl in *.
    - f_equal.
      destruct (decide (m <= n0)), (leb_spec m n0), (ltb_spec n0 (n + m));
        try discriminate; try lia.
      + destruct (decide (m <= n0 - n)); lia.
      + destruct (decide (m <= n0)); lia.
    - apply orb_false_elim in L. intuition congruence.
    - intuition congruence.
  Qed.

  Fixpoint beta_reduction m (t : tm) : tm :=
    match t with
    | tm_app (tm_abs T t) s =>
        subst_last m (beta_reduction m s) (beta_reduction (S m) t)
    | tm_app s t => tm_app (beta_reduction m s) (beta_reduction m t)
    | tm_abs T t => tm_abs T (beta_reduction (S m) t)
    | x => x
    end.

  Fixpoint eta_reduction m (t : tm) {struct t} : tm :=
    match t with
    | tm_abs T (tm_app t (tm_lvl n)) =>
        if andb (eqb n m) (negb (contains_bound_levels m 1 t)) then
          bound_level_map (fun x => x - 1) m t
          else tm_abs T (tm_app (eta_reduction (S m) t) n)
    | tm_app s t => tm_app (eta_reduction m s) (eta_reduction m t)
    | tm_abs T t => tm_abs T (eta_reduction (S m) t)
    | x => x
    end.


  Theorem has_type_beta_reduction C T t :
    has_type C t T ->
    has_type C (beta_reduction |(C)| t) T.
  Proof.
    generalize dependent T. generalize dependent C.
    induction t; intros C T HT; try assumption.
    - destruct t1; try solve
        [inversion HT; subst; econstructor; eauto].
      inversion HT. subst.
      simpl. eapply has_type_subst_last; [|eauto].
      apply IHt1 in H2. simpl in H2. inversion H2. subst.
      apply ty_arr_inj in H5. destruct H5. now subst.
    - inversion HT. subst.
      simpl. constructor.
      specialize IHt with (C +: t0) B.
      rewrite rlength_rcons in IHt.
      auto.
  Qed.

  Theorem has_type_eta_reduction C T t :
    has_type C t T ->
    has_type C (eta_reduction |(C)| t) T.
  Proof.
    generalize dependent T. generalize dependent C.
    induction t; intros C T HT; try assumption;
    inversion HT; subst; try solve [econstructor; eauto].
    assert (IH := IHt (C +: t0)). rewrite rlength_rcons in IH.
    destruct t1; try solve [econstructor; eauto].
    simpl in IH.
    destruct t1_2; try solve [constructor; auto]. simpl.
    destruct (eqb_spec n |(C)|);
    destruct (contains_bound_levels |(C)| 1 t1_1) eqn : E;
      try solve [constructor; auto].
    simpl in *. inversion H3. subst.
    inversion H5. subst.
    rewrite @lookup_rcons_eq in H1; [|lia].
    injection H1. intros ->.
    eapply has_type_bound_level_map2.
    3:{ rewrite bound_level_map_id; eassumption. }
    - now rewrite rlength_rcons.
    - intros. now rewrite lookup_rcons_lt.
  Qed.
End Stlc.


(****************)
(** ** Examples *)
(****************)

Module StlcChurch.
  Module Stlc := Stlc TyChurch RlistList.
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
  Compute subst_last 1 tm_bot <{ \: o, 1 }>.

  (** Reduction *)
  Compute beta_reduction 1 <{ (\: o, 1) 0 }>.
  Compute beta_reduction 0 <{ (\: o -> o, 0) (\: o, 0) }>.
  Compute beta_reduction 0 <{ (\: o -> o, 0) ((\: o -> o, 0) (\: o, 0)) }>.
End StlcChurch.
