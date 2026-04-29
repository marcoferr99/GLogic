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
    | gtm_nom : ty -> nat -> gtm
    | gtm_prd : list ty -> nat -> gtm.

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
    gtm_rect P l a b (o gtm_bot I) (o gtm_top I) (o gtm_and I) (o gtm_or I) (o gtm_imp I) (fun t => o (gtm_for t) I) (fun t => o (gtm_ex t) I) (fun t => o (gtm_nab t) I) (fun t n => o (gtm_nom t n) I) (fun l n => o (gtm_prd l n) I).

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
    | gtm_prd l n => foldr ty_arr ty_prp l
    | _ => ty_prp
    end.

  Definition tm_eq_dec_other a b :
    tm_other a -> tm_other b -> Decision (a = b).
  Proof. ltac1:(solve_decision). Qed.
End GStlc.


Module GStlcTheories.
  Module StlcTheories := StlcTheories GStlc.
  Export StlcTheories.


  Coercion gtm_lvl : nat >-> gtm.

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
  Notation "n ^ T" := (gtm_nom T n) (in custom stlc_tm at level 200) : stlc_scope.


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

  (** Replace nominal variables with other nominal variables of the same type *)
  Fixpoint nom_map (f : ty -> nat -> nat) t : tm :=
    match t with
    | gtm_nom T a => gtm_nom T (f T a)
    | gtm_abs T t => gtm_abs T (nom_map f t)
    | gtm_app s t => gtm_app (nom_map f s) (nom_map f t)
    | x => x
    end.

  Definition pointwise2_Equiv {A B C} : Equiv (A -> B -> C) :=
    fun f g => forall x y, f x y = g x y.

  Theorem nom_map_Proper : Proper (pointwise2_Equiv ==> (=) ==> (=)) nom_map.
  Proof.
    intros f g E ? t ->. induction t; simpl; try (easy); congruence.
  Qed.

  Theorem nom_map_comp f g t :
    nom_map f (nom_map g t) = nom_map (fun T x => f T (g T x)) t.
  Proof.
    induction t; simpl; try (easy); congruence.
  Qed.

  Theorem level_prop_nom_map P f t :
    level_prop P (nom_map f t) <-> level_prop P t.
  Proof.
    induction t; simpl; try (easy).
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
    induction t; try (easy); simpl; congruence.
  Qed.

  (*
  Hint Rewrite nom_map_app nom_map_id : tm.
  *)
  Hint Rewrite nom_map_id : tm.

  Ltac2 Notation "gnorm" :=
    Control.enter (fun () =>
      change gtm_app with tm_app in *;
      change gtm_abs with tm_abs in *
    ).

  Theorem has_type_nom_map1 f C T t :
    has_type C (nom_map f t) T -> has_type C t T.
  Proof.
    revert C T.
    induction t; intros C T H; tm_simpl in *; gnorm; auto; has_type; auto.
    - eexists; first [apply IHt1|apply IHt2]; eassumption.
  Qed.

  Theorem has_type_nom_map2 f C T t :
    has_type C t T -> has_type C (nom_map f t) T.
  Proof.
    revert C T.
    induction t; intros C T H; tm_simpl in *; gnorm; auto; has_type; auto.
    - eexists; first [apply IHt1|apply IHt2]; eassumption.
  Qed.

  Theorem has_type_nom_map f C T t :
    has_type C (nom_map f t) T <-> has_type C t T.
  Proof.
    split.
    - apply has_type_nom_map1.
    - apply has_type_nom_map2.
  Qed.

  Theorem level_map_nom_map f g t :
    level_map g (nom_map f t) = nom_map f (level_map g t).
  Proof.
    induction t; try easy; tm_simpl; gnorm; tm_simpl; now f_equal.
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
    induction t; intros m h; try easy; tm_simpl; gnorm; tm_simpl.
    - unfold lookup_default. simpl. destruct (decide (n < h)).
      + now rewrite decide_True.
      + now rewrite decide_False.
    - now f_equal.
    - rewrite IHt. f_equal. apply subst_Proper > [|reflexivity].
      constructor > [reflexivity|].
      intros n Hn. simpl in *. destruct (decide (n < h)).
      + rewrite decide_True > [|easy]. symmetry. apply level_map_nom_map.
      + rewrite decide_False; easy.
  Qed.

  Theorem nom_map_subst_last f n m s t :
    nom_map f (subst_last n m s t) = subst_last n m (nom_map f s) (nom_map f t).
  Proof.
    unfold subst_last. rewrite nom_map_subst.
    apply subst_Proper > [|reflexivity].
    simpl. constructor > [reflexivity|].
    intros a Ha. simpl in *. now destruct (decide (a < n)).
  Qed.

  Hint Rewrite nom_map_subst_last : tm.

  Theorem lambda_equiv_nom_map m a b f :
    lambda_equiv m a b -> lambda_equiv m (nom_map f a) (nom_map f b).
  Proof.
    intros H.
    eapply rtsc_congruence > [|eassumption]. clear H.
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
      + apply IHt1 > [lia|assumption].
      + apply IHt2 > [lia|assumption].
    - auto.
    - injection N. lia.
  Qed.

  Theorem nom_fresh_in_supp t T : ~ in_supp t (gtm_nom T (nom_fresh t)).
  Proof. now apply nom_fresh_le_in_supp. Qed.

  Theorem nom_in_supp b T : exists a, ~ in_supp b (gtm_nom T a).
  Proof. eexists. apply nom_fresh_in_supp. Qed.

  Theorem in_supp_not B n :
    in_supp <{ ~ B }> n <-> in_supp B n.
  Proof. unfold in_supp. simpl. intuition. Qed.


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
        ltac1:(replace b with (nom_map g (nom_map f b))) > [now apply lambda_equiv_nom_map|].
        rewrite <- (nom_map_id b) at 2.
        rewrite nom_map_comp. now apply nom_map_Proper.
    - intros y z [f g Hgf Hfg] [h l Hlh Hhl].
      eapply (tm_equiv_intro (fun T x => f T (h T x)) (fun T x => l T (g T x)));
        try (congruence).
      etransitivity > [eassumption|].
      rewrite <- (nom_map_comp f h).
      now apply lambda_equiv_nom_map.
  Qed.


  (***************************)
  (** ** Nominal Abstraction *)
  (***************************)


  (** Replace the nominal variable [gtm_nom A n] with a variable binding *)
  Definition nom_bind m n t : tm :=
    tm_abs (type_check_other n) ((fix fx t := match t with
    | gtm_nom _ _ => if decide (t = n) then tm_lvl m else t
    | gtm_abs T t => gtm_abs T (fx t)
    | gtm_app s t => gtm_app (fx s) (fx t)
    | x => x
    end) (lift m t)).

  Definition nom_binds m (l : list tm) t : tm :=
    fold_right (nom_bind m) t l.

  Definition nominal_abstraction m s t : Prop :=
    exists l, lambda_equiv m s (nom_binds m l t).

  Example nominal_abstraction_ex1 m T n :
    nominal_abstraction m (tm_abs T m) (gtm_nom T n).
  Proof.
    exists [gtm_nom T n].
    simpl. unfold nom_bind. simpl.
    rewrite (decide_True); reflexivity.
  Qed.

  Example nominal_abstraction_ex2 m a A b B :
    <{a^A}> <> <{b^B}> ->
    nominal_abstraction m <{\: A, m (b^B)}> <{(a^A) (b^B)}>.
  Proof.
    exists [gtm_nom A a].
    simpl. unfold nom_bind. simpl.
    rewrite (decide_True) by reflexivity.
    now rewrite (decide_False).
  Qed.

  Example nominal_abstraction_ex3 m a A b B :
    <{a^A}> <> <{b^B}> ->
    nominal_abstraction m <{\: A, \: B, m $(S m)}> <{(a^A) (b^B)}>.
  Proof.
    exists [gtm_nom A a; gtm_nom B b].
    simpl. unfold nom_bind. simpl.
    rewrite (decide_False) by easy.
    rewrite (decide_True) by reflexivity.
    simpl.
    rewrite (decide_True) by reflexivity.
    rewrite (decide_True) by reflexivity.
    reflexivity.
  Qed.
End GStlcTheories.
