Require Export stlc.

Import Lia.


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
  Notation "⊥" := gtm_bot (in custom stlc_tm) : stlc_scope.
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
  Notation "∇ T , t" := (tm_app (gtm_nab T) (tm_abs T t))
    (in custom stlc_tm at level 200, T custom stlc_ty,
      t custom stlc_tm at level 200, left associativity) : stlc_scope.
  Notation "B ≡ C" := (<{(B > C) /\ (C > B)}>) (in custom stlc_tm at level 80) : stlc_scope.
  Notation "~ B" := <{ B > gtm_bot }> (in custom stlc_tm at level 75) : stlc_scope.


  (**************************************)
  (** ** Nominal constants manipulation *)
  (**************************************)

  Fixpoint nom_prop (P : ty -> nat -> Prop) t : Prop :=
    match t with
    | gtm_nom T n => P T n
    | gtm_app a b => nom_prop P a \/ nom_prop P b
    | gtm_abs A a => nom_prop P a
    | _ => False
    end.

  Fixpoint nom_map (f : ty -> nat -> nat) t : tm :=
    match t with
    | gtm_nom T a => gtm_nom T (f T a)
    | gtm_abs T t => gtm_abs T (nom_map f t)
    | gtm_app s t => gtm_app (nom_map f s) (nom_map f t)
    | x => x
    end.

  Instance pointwise2_Equiv A B C : Equiv (A -> B -> C) :=
    fun f g => forall x y, f x y = g x y.

  Theorem nom_map_Proper : Proper ((≡) ==> (=) ==> (=)) nom_map.
  Proof.
    intros f g E ? t ->. induction t; simpl; try easy; congruence.
  Qed.

  Theorem nom_map_comp f g t :
    nom_map f (nom_map g t) = nom_map (fun T x => f T (g T x)) t.
  Proof.
    induction t; simpl; try easy; congruence.
  Qed.

  Theorem level_prop_nom_map P f t :
    level_prop P (nom_map f t) <-> level_prop P t.
  Proof.
    induction t; simpl; try easy.
    tm_simpl. intuition.
  Qed.

  Hint Rewrite level_prop_nom_map : tm.

  (*
  Theorem nom_map_app f s t :
    nom_map f (tm_app s t) = tm_app (nom_map f s) (nom_map f t).
  Proof. reflexivity. Qed.
  *)

  Theorem nom_map_id t : nom_map (fun _ => id) t = t.
  Proof.
    induction t; try easy; simpl; congruence.
  Qed.

  (*
  Hint Rewrite nom_map_app nom_map_id : tm.
  *)
  Hint Rewrite nom_map_id : tm.

  Theorem has_type_nom_map f C T t :
    has_type C (nom_map f t) T <->
    has_type C t T.
  Proof.
    revert C T.
    induction t; intros C T; tm_simpl; try easy.
    - split; intros [A]; exists A; now first [apply IHt1|apply IHt2].
    - split; intros [B]; exists B; now try apply IHt.
    - split; intros H; inversion H; subst; now tm_simpl.
  Qed.

  Theorem level_map_nom_map f g t :
    level_map g (nom_map f t) = nom_map f (level_map g t).
  Proof.
    induction t; try easy; tm_simpl; now f_equal.
  Qed.

  (*
  Theorem nom_map_lift f m t :
    nom_map f (lift m t) = lift m (nom_map f t).
  Proof.
    induction t; try easy.
    - unfold lift, bound_level_map in *. rewrite level_map_app.
      rewrite nom_map_app. rewrite IHt1, IHt2. now tm_simpl.
    - unfold lift, bound_level_map in *. rewrite level_map_abs.
      tm_simpl. now rewrite IHt.
  Qed.
  *)

  Theorem nom_map_subst f m l t :
    nom_map f (subst m l t) = subst m (nom_map f <$> l) (nom_map f t).
  Proof.
    revert m l.
    induction t; intros m l; try easy; tm_simpl.
    - unfold lookup_default. simpl. destruct (decide (n < l)).
      + now rewrite decide_True.
      + now rewrite decide_False.
    - now f_equal.
    - rewrite IHt. f_equal. apply subst_Proper; [|reflexivity].
      constructor; [reflexivity|].
      intros n Hn. simpl in *. destruct (decide (n < l)).
      + rewrite decide_True; [|easy]. symmetry. apply level_map_nom_map.
      + rewrite decide_False; easy.
  Qed.

  Theorem nom_map_subst_last f n m s t :
    nom_map f (subst_last n m s t) = subst_last n m (nom_map f s) (nom_map f t).
  Proof.
    unfold subst_last. rewrite nom_map_subst.
    apply subst_Proper; [|reflexivity].
    simpl. constructor; [reflexivity|].
    intros a Ha. simpl in *. now destruct (decide (a < n)).
  Qed.

  Hint Rewrite nom_map_subst_last : tm.

  Theorem lambda_equiv_nom_map m a b f :
    lambda_equiv m a b -> lambda_equiv m (nom_map f a) (nom_map f b).
  Proof.
    intros H.
    eapply rtsc_congruence; [|eassumption]. clear H.
    intros x y H.
    induction H; subst.
    - constructor. destruct H; destruct H; simpl.
      + left. rewrite nom_map_subst_last. constructor.
      + right. unfold bound_level_map. rewrite <- level_map_nom_map.
        constructor. unfold contains_bound_levels. now tm_simpl.
    - tm_simpl. now apply step_appL.
    - tm_simpl. now apply step_appR.
    - tm_simpl. now apply step_abs.
  Qed.


  (** *** Support *)

  Definition in_supp t n := nom_prop (fun T x => n = gtm_nom T x) t.

  (*
  Theorem in_supp_app a b n :
    in_supp (tm_app a b) n <-> in_supp a n \/ in_supp b n.
  Proof. reflexivity. Qed.

  Hint Rewrite in_supp_app : tm.
  *)

  Theorem in_supp_other t n : in_supp t n -> tm_other n.
  Proof.
    intros H. unfold in_supp in H.
    induction t; try easy; tm_simpl in H; intuition.
    now subst.
  Qed.

  Fixpoint nom_fresh t : nat :=
    match t with
    | gtm_nom _ n => S n
    | gtm_app a b => max (nom_fresh a) (nom_fresh b)
    | gtm_abs A a => nom_fresh a
    | _ => 0
    end.

  Theorem nom_fresh_le_in_supp t T :
    forall n, nom_fresh t <= n -> ~ in_supp t (gtm_nom T n).
  Proof.
    intros n Hn N.
    induction t; unfold in_supp in *; simpl in *; try easy.
    - destruct N.
      + apply IHt1; [lia|assumption].
      + apply IHt2; [lia|assumption].
    - auto.
    - injection N. lia.
  Qed.

  Theorem nom_fresh_in_supp t T : ~ in_supp t (gtm_nom T (nom_fresh t)).
  Proof. now apply nom_fresh_le_in_supp. Qed.


  (************************)
  (** ** Term equivalence *)
  (************************)

  Inductive tm_equiv m a b : Prop :=
    tm_equiv_intro f g :
      (forall T x, g T (f T x) = x) -> (forall T x, f T (g T x) = x) ->
      lambda_equiv m a (nom_map f b) ->
      tm_equiv m a b.
  Arguments tm_equiv_intro {m a b}.

  Instance tm_equiv_equivalence m : Equivalence (tm_equiv m).
  Proof.
    constructor; intros a.
    - eapply (tm_equiv_intro (fun _ x => x)); try reflexivity.
      now tm_simpl.
    - intros b [f g Hgf Hfg]. econstructor.
      + apply Hfg.
      + apply Hgf.
      + symmetry.
        replace b with (nom_map g (nom_map f b)); [now apply lambda_equiv_nom_map|].
        rewrite <- (nom_map_id b) at 2.
        rewrite nom_map_comp. now apply nom_map_Proper.
    - intros y z [f g Hgf Hfg] [h l Hlh Hhl].
      eapply (tm_equiv_intro (fun T x => f T (h T x)) (fun T x => l T (g T x)));
        try congruence.
      etransitivity; [eassumption|].
      rewrite <- (nom_map_comp f h).
      now apply lambda_equiv_nom_map.
  Qed.

  (*
  Definition nom_swap (T : ty) (n m : nat) A a :=
    if (decide (A = T)) then (
      if (decide (a = n)) then m else (
        if (decide (a = m)) then n else a
      )
    ) else a.

  Theorem nom_swap_eq T n m : nom_swap T n m T n = m.
  Proof.
    unfold nom_swap. now repeat rewrite decide_True.
  Qed.

  Theorem nom_swap_neq T n m A x :
    x <> n -> x <> m -> nom_swap T n m A x = x.
  Proof.
    intros. unfold nom_swap. destruct (decide (A = T)); [|reflexivity].
    now repeat rewrite decide_False.
  Qed.

  Hint Rewrite nom_swap_eq : tm.

  Theorem in_supp_nom_map f t :
    (forall T n, in_supp t (gtm_nom T n) -> f T n = n) ->
    nom_map f t = t.
  Proof.
    intros H. induction t; simpl in *; try reflexivity.
    - rewrite IHt1, IHt2; try reflexivity.
      + intros. apply H. unfold in_supp in *. simpl. intuition.
      + intros. apply H. unfold in_supp in *. simpl. intuition.
    - rewrite IHt; [reflexivity|].
      intros. auto.
    - f_equal. now apply H.
  Qed.

  Theorem in_supp_nom_swap T m n t :
    ~ in_supp t (gtm_nom T n) -> ~ in_supp t (gtm_nom T m) ->
    nom_map (nom_swap T m n) t = t.
  Proof.
    intros. apply in_supp_nom_map. intros.
    destruct (decide (T = T0)).
    - subst. apply nom_swap_neq; intros N; subst; contradiction.
    - unfold nom_swap. now rewrite decide_False.
  Qed.

  Theorem nom_swap_tm_equiv m T x y a b :
    lambda_equiv m a (nom_map (nom_swap T x y) b) -> tm_equiv m a b.
  Proof.
    intros LE.
    apply (tm_equiv_intro (nom_swap T x y) (nom_swap T y x)); try assumption.
    - intros X t. unfold nom_swap.
      destruct (decide (X = T)); [|reflexivity].
      destruct (decide (t = x)), (decide (t = y)), (decide (x = y)); subst;
        try (now rewrite decide_True).
      + reflexivity.
      + now repeat rewrite decide_False.
      + now repeat rewrite decide_False.
    - intros X t. unfold nom_swap.
      destruct (decide (X = T)); [|reflexivity].
      destruct (decide (t = x)), (decide (t = y)), (decide (y = x)); subst;
        try (now rewrite decide_True).
      + reflexivity.
      + now repeat rewrite decide_False.
      + now repeat rewrite decide_False.
  Qed.
  *)

  (*
  Theorem has_type_tm_equiv (C : context) T a b : tm_equiv C a b ->
    has_type C a T -> has_type C b T.
  Proof.
    intros TE HT. induction TE.
    eapply has_type_nom_map.
    eapply has_type_lambda_equiv; eassumption.
  Qed.
  *)


  (*
  Theorem subst_gtm_bot n l : subst n l gtm_bot = gtm_bot.
  Proof. now tm_simpl. Qed.

  Theorem subst_last_gtm_bot m n s : subst_last m n s gtm_bot = gtm_bot.
  Proof. now tm_simpl. Qed.

  Hint Rewrite subst_gtm_bot subst_last_gtm_bot : tm.
  *)
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
