Require Export stlc_types.
From stdpp Require Export relations.


(***********************************)
(** * Simply Typed Lambda Calculus *)
(***********************************)


(*****************)
(** ** Interface *)
(*****************)

Declare Custom Entry stlc_tm.

Module Type STLC.
  Declare Module Ty : TY.
  Module TyTheories := TyTheories Ty.
  Export TyTheories.


  Parameter tm : Set.
  Parameter tm_lvl : nat -> tm.
  Parameter tm_app : tm -> tm -> tm.
  Parameter tm_abs : ty -> tm -> tm.
  Parameter tm_other : tm -> Prop.

  Parameter tm_rect :
    forall P : tm -> Type,
    (forall n, P (tm_lvl n)) ->
    (forall s, P s -> forall t, P t -> P (tm_app s t)) ->
    (forall T t, P t -> P (tm_abs T t)) ->
    (forall t, tm_other t -> P t) ->
    forall t, P t.

  Axiom tm_rect_lvl : forall P l a b o n, tm_rect P l a b o (tm_lvl n) = l n.
  Axiom tm_rect_app : forall P l a b o s t,
    tm_rect P l a b o (tm_app s t) = a _ (tm_rect P l a b o s) _ (tm_rect P l a b o t).
  Axiom tm_rect_abs : forall P l a b o T t,
    tm_rect P l a b o (tm_abs T t) = b T _ (tm_rect P l a b o t).
  Axiom tm_rect_other : forall t P l a b o,
    forall O : tm_other t, tm_rect P l a b o t = o t O.


  Parameter type_check_other : tm -> ty.
End STLC.


(****************)
(** ** Theories *)
(****************)

Module StlcTheories (Stlc : STLC).
  Export Stlc.


  Coercion tm_lvl : nat >-> tm.

  Definition tm_rec (P : tm -> Set) := tm_rect P.
  Definition tm_ind (P : tm -> Prop) := tm_rect P.

  (** Tactics *)
  Create HintDb tm.
  Hint Rewrite tm_rect_lvl tm_rect_app tm_rect_abs : tm.
  Hint Rewrite tm_rect_other using assumption : tm.
  Ltac2 tm_simpl c := autorewrite @tm c; s_simpl c.
  Ltac2 Notation "tm_simpl" "in" "*" := Control.enter (fun () => tm_simpl all).
  Ltac2 Notation "tm_simpl" "in" h(ident) := tm_simpl (one_hyp h).
  Ltac2 Notation "tm_simpl" := tm_simpl goal.
  Ltac2 Notation "tm_induction" h(constr) := induction $h using tm_ind.


  (** *** View *)

  Inductive tmv : Set :=
    | tmv_lvl : nat -> tmv
    | tmv_app : tmv -> tmv -> tmv
    | tmv_abs : ty -> tmv -> tmv
    | tmv_other : tm -> tmv.

  Definition to_tmv : tm -> tmv :=
    tm_rec _
      (fun n => tmv_lvl n)
      (fun s fs t ft => tmv_app fs ft)
      (fun T t ft => tmv_abs T ft)
      (fun t _ => tmv_other t).

  Theorem to_tmv_lvl n : to_tmv (tm_lvl n) = tmv_lvl n.
  Proof. unfold to_tmv. now tm_simpl. Qed.

  Theorem to_tmv_app s t : to_tmv (tm_app s t) = tmv_app (to_tmv s) (to_tmv t).
  Proof. unfold to_tmv. now tm_simpl. Qed.

  Theorem to_tmv_abs T t : to_tmv (tm_abs T t) = tmv_abs T (to_tmv t).
  Proof. unfold to_tmv. now tm_simpl. Qed.

  Theorem to_tmv_other t : tm_other t -> to_tmv t = tmv_other t.
  Proof. intros. unfold to_tmv. now tm_simpl. Qed.

  Create HintDb tmv.
  Hint Rewrite to_tmv_lvl to_tmv_app to_tmv_abs : tmv.
  Hint Rewrite to_tmv_other using assumption : tmv.
  Ltac2 tmv_simpl c := autorewrite @tmv c; s_simpl c.
  Ltac2 Notation "tmv_simpl" "in" "*" := Control.enter (fun () => tmv_simpl all).
  Ltac2 Notation "tmv_simpl" "in" h(ident) := tmv_simpl (one_hyp h).
  Ltac2 Notation "tmv_simpl" := tmv_simpl goal.

  Fixpoint to_tm t : tm :=
    match t with
    | tmv_lvl n => tm_lvl n
    | tmv_app a b => tm_app (to_tm a) (to_tm b)
    | tmv_abs T t => tm_abs T (to_tm t)
    | tmv_other t => t
    end.

  Theorem to_tm_to_tmv t : to_tm (to_tmv t) = t.
  Proof.
    tm_induction t; tmv_simpl; congruence.
  Qed.

  Hint Rewrite to_tm_to_tmv : tmv.


  (** *** Injection and discriminate *)

  Theorem to_tmv_inj a b : to_tmv a = to_tmv b -> a = b.
  Proof.
    intros H. apply (f_equal to_tm) in H.
    now (tmv_simpl in H).
  Qed.

  Theorem tm_lvl_inj {n m} : tm_lvl n = tm_lvl m -> n = m.
  Proof.
    intros H. apply (f_equal to_tmv) in H.
    tmv_simpl in H. now injection H.
  Qed.

  Theorem tm_app_inj {a b c d} : tm_app a b = tm_app c d -> a = c /\ b = d.
  Proof.
    intros H. apply (f_equal to_tmv) in H.
    tmv_simpl in H. injection H. intros.
    split; now apply to_tmv_inj.
  Qed.

  Theorem tm_abs_inj {A a B b} : tm_abs A a = tm_abs B b -> A = B /\ a = b.
  Proof.
    intros H. apply (f_equal to_tmv) in H. tmv_simpl in H.
    injection H. intros. intuition. now apply to_tmv_inj.
  Qed.

  Ltac2 Notation "tm_injection" h(ident) :=
    Control.enter (fun () =>
      let c := Control.hyp h in c_injection [(fun () => 'tm_lvl_inj); (fun () => 'tm_app_inj); (fun () => 'tm_abs_inj)] c
    ).

  Ltac2 tm_discriminate_f x :=
    lazy_match! x with
    | tm_lvl _ => '(tm_rect _ (fun _ => True) (fun _ _ _ _ => False)
      (fun _ _ _ => False) (fun _ _ => False))
    | tm_app _ _ => '(tm_rect _ (fun _ => False) (fun _ _ _ _ => True)
      (fun _ _ _ => False) (fun _ _ => False))
    | tm_abs _ _ => '(tm_rect _ (fun _ => False) (fun _ _ _ _ => False)
      (fun _ _ _ => True) (fun _ _ => False))
    | _ => '(tm_rect _ (fun _ => False) (fun _ _ _ _ => False)
      (fun _ _ _ => False) (fun _ _ => True))
    end.

  Ltac2 tm_discriminate_rew h :=
    repeat (first [
      rewrite tm_rect_lvl in $h
    | rewrite tm_rect_app in $h
    | rewrite tm_rect_abs in $h
    | rewrite tm_rect_other in $h by assumption
    ]).

  Ltac2 tm_discriminate h :=
    let disc := c_discriminate tm_discriminate_f tm_discriminate_rew in
    let c := Control.hyp h in
    lazy_match! (Constr.type c) with
    | tm_other ?x => let a := Fresh.in_goal @a in let e := Fresh.in_goal @E in
        remember $x as $a eqn : $e; disc e
    | _ => disc h
    end.

  Ltac2 Notation "tm_discriminate" h(ident) := tm_discriminate h.
  Ltac2 Notation "tm_discriminate" := first_hyp tm_discriminate.


  (**************)
  (** ** Typing *)
  (**************)

  Inductive has_type : context -> tm -> ty -> Prop :=
    | ht_lvl (c : context) n : n < c -> has_type c (tm_lvl n) (c n)
    | ht_app c A B s t : has_type c s (ty_arr A B) -> has_type c t A ->
        has_type c (tm_app s t) B
    | ht_abs c A B t : has_type (c +: A) t B ->
        has_type c (tm_abs A t) (ty_arr A B)
    | ht_other c t : tm_other t -> has_type c t (type_check_other t).

  Theorem ht_other2 c T t :
    tm_other t -> T = type_check_other t ->
    has_type c t T.
  Proof. intros ? ->. now constructor. Qed.

  Theorem has_type_lvl : forall {c n T},
    has_type c (tm_lvl n) T <-> n < c /\ c n = T.
  Proof.
    split; intros H.
    - inversion H; try (tm_discriminate).
      subst. now tm_injection H0.
    - destruct H. subst. now constructor.
  Qed.

  Theorem has_type_app : forall {c s t B},
    has_type c (tm_app s t) B <->
    exists2 A, has_type c s -[ A -> B ]- & has_type c t A.
  Proof.
    split; intros H.
    - inversion H; try (tm_discriminate).
      subst. tm_injection H0. now exists A.
    - destruct H. econstructor; eauto.
  Qed.

  Theorem has_type_abs : forall {c A T t},
    has_type c (tm_abs A t) T <->
    exists2 B, has_type (c +: A) t B & T = -[ A -> B ]-.
  Proof.
    split; intros H.
    - inversion H; subst; try (tm_discriminate).
      tm_injection H0. now exists B.
    - destruct H. subst. now constructor.
  Qed.

  Theorem has_type_abs1 {C A B t} :
    has_type (C +: A) t B -> has_type C (tm_abs A t) -[ A -> B ]-.
  Proof. intros H. apply has_type_abs. eauto. Qed.

  Theorem has_type_abs2 {C A B T t} :
    has_type C (tm_abs T t) -[ A -> B ]- ->
    has_type (C +: A) t B.
  Proof.
    intros H. apply has_type_abs in H as [].
    now ty_injection H0.
  Qed.

  Theorem has_type_other {t T C} :
    tm_other t ->
    has_type C t T <-> T = type_check_other t.
  Proof.
    intros O. split; intros H.
    - inversion H; subst; try (tm_discriminate). reflexivity.
    - subst. now constructor.
  Qed.

  Theorem has_type_other1 {c t T} :
    tm_other t -> has_type c t T ->
    T = type_check_other t.
  Proof. apply has_type_other. Qed.


  (** *** Typing tactics *)

  Ltac2 ht_lvl (h : ident) : ident list :=
    let c := Control.hyp h in
    let i1 := Fresh.in_goal @L in let i2 := Fresh.in_goal @E in
    destruct (proj1 has_type_lvl $c) as [$i1 $i2]; [].

  Ltac2 ht_app h :=
    let c := Control.hyp h in
    let hs := Fresh.in_goal @Hs in let ht := Fresh.in_goal @Ht in
    destruct (proj1 has_type_app $c) as [? $hs $ht]; [hs; ht].

  Ltac2 ht_abs1 h :=
    let c := Control.hyp h in
    let h1 := Fresh.in_goal @H in
    assert ($h1 := has_type_abs2 $c); [h1].

  Ltac2 ht_abs2 h :=
    let c := Control.hyp h in
    let h1 := Fresh.in_goal @H in
    let e := Fresh.in_goal @E in
    destruct (proj1 has_type_abs $c) as [? $h1 $e];
    let ce := Control.hyp e in try (rewrite $ce in *); [h1].

  Ltac2 ht_other h :=
    let c := Control.hyp h in
    lazy_match! Constr.type c with
    | has_type _ ?t _ =>
        let ot := Fresh.in_goal @O in assert ($ot : tm_other $t) by easy;
        let o := Control.hyp ot in
        let a := Fresh.in_goal @H in
        assert ($a := has_type_other1 $o $c); simpl in $a; try (ty_injection $a);
        let ca := Control.hyp a in try (rewrite $ca in *); []
    end.

  (*
  Ltac2 ht_other h :=
    let c := Control.hyp h in
    lazy_match! Constr.type c with
    | has_type _ ?t _ =>
        let op := List.find_opt (fun (_, _, ty) => Constr.equal ty '(tm_other $t)) (Control.hyps ()) in
        match op with
        | None => Control.zero No_value
        | Some o =>
            let oc := Control.hyp (match o with (x, _, _) => x end) in
            let a := Fresh.in_goal @H in
            assert ($a := has_type_other1 $oc $c);
            let ca := Control.hyp a in try (rewrite $ca in * ); []
        end
    end.
    *)

  Ltac2 ht_first := fun x => c_first (fun f => f x) [ht_lvl; ht_app; ht_abs1; ht_abs2; ht_other].


  Ltac2 htg_lvl () := refine '(proj2 has_type_lvl _).
  Ltac2 htg_app () := refine '(proj2 has_type_app _).
  Ltac2 htg_abs1 () := refine '(has_type_abs1 _).
  Ltac2 htg_other () :=
    lazy_match! Control.goal () with
    | has_type _ ?t _ =>
        let ot := Fresh.in_goal @O in assert ($ot : tm_other $t) by easy;
        let o := Control.hyp ot in
        refine '(proj2 (has_type_other $o) _); try reflexivity
    end.

  Ltac2 mutable htg_list () := [htg_lvl; htg_app; htg_abs1; htg_other].
  Ltac2 has_type_goal () := first0 (htg_list ()).

  (*
  Ltac2 has_type_goal () :=
  Ltac2 mutable has_type_goal () :=
    lazy_match! (Control.goal ()) with
    | has_type _ (tm_lvl _) _ => apply has_type_lvl
    | has_type _ (tm_app _ _) _ => apply has_type_app
    | has_type _ (tm_abs _ _) (ty_arr _ _) => apply ht_abs; subst
    | has_type _ (tm_abs _ _) _ => apply has_type_abs; subst
    | has_type _ _ _ => apply has_type_other > [assumption|]; reflexivity
    end.
  *)

  Ltac2 has_type h := i_iter ht_first [h].
  Ltac2 Notation "has_type" "in" h(ident) := has_type h.
  Ltac2 Notation "has_type" :=
    Control.enter (fun () => all_hyps (fun h => try (has_type h)); repeat (has_type_goal ())).


  (** *** Other typing lemmas *)

  Theorem has_type_unique {A B} C t :
    has_type C t A -> has_type C t B -> A = B.
  Proof.
    revert B A C.
    tm_induction t; intros C A B HA HB; has_type;
      try ltac1:(intuition congruence).
    - eapply IHt1 in Hs0 > [|apply Hs]. now (ty_injection Hs0).
    - f_equal. eauto.
  Qed.

  (*
  Ltac has_type_unique :=
    match goal with
      [H1 : has_type ?C ?t _, H2 : has_type ?C ?t _ |- _] => generalize (has_type_unique _ _ H1 H2); let x := fresh "H" in intros x; ty_injection x
    end.

  Ltac has_type_other :=
    match goal with
      [H : has_type ?C ?t ?T |- _] => apply has_type_other in H; [|reflexivity]; ty_injection H
    end.

  Tactic Notation "has_type" "in" ident(H) :=
    match type of H with
    | has_type _ (tm_app _ _) _ => apply has_type_app in H as []; try has_type_unique; try has_type_other
    | has_type _ (tm_abs _ _) _ => apply has_type_abs2 in H
    end; ty_simpl in H.

  Tactic Notation "has_type" :=
    repeat match goal with [H : has_type ?C ?t ?T |- _] => has_type in H end.
    *)


  (**************************)
  (** ** Level manipulation *)
  (**************************)

  Definition level_prop (P : nat -> Prop) t : Prop :=
    (fix fx P t :=
      match t with
      | tmv_lvl m => P m
      | tmv_abs T s => fx P s
      | tmv_app s1 s2 => fx P s1 \/ fx P s2
      | _ => False
    end) P (to_tmv t).

  Theorem level_prop_lvl P (n : nat) : level_prop P n <-> P n.
  Proof. unfold level_prop. now tmv_simpl. Qed.

  Theorem level_prop_app P s t :
    level_prop P (tm_app s t) <-> level_prop P s \/  level_prop P t.
  Proof. unfold level_prop. tmv_simpl. auto. Qed.

  Theorem level_prop_abs P T t :
    level_prop P (tm_abs T t) <-> level_prop P t.
  Proof. unfold level_prop. now tmv_simpl. Qed.

  Theorem level_prop_other P t : tm_other t -> ~ level_prop P t.
  Proof. intros. unfold level_prop. now tmv_simpl. Qed.

  Hint Rewrite level_prop_lvl level_prop_app level_prop_abs : tm.

  Definition contains_bound_levels m n :=
    level_prop (fun x => m <= x /\ x < (n + m)).


  (** Apply "f" to all variables in the term "t" *)
  Definition level_map (f : nat -> nat) (t : tm) : tm :=
    (fix fx f x :=
      match x with
      | tmv_lvl n => tm_lvl (f n)
      | tmv_app a b => tm_app (fx f a) (fx f b)
      | tmv_abs T t => tm_abs T (fx f t)
      | tmv_other t => t
    end) f (to_tmv t).

  Theorem level_map_lvl f n : level_map f (tm_lvl n) = f n.
  Proof. unfold level_map. now tmv_simpl. Qed.

  Theorem level_map_app f s t :
    level_map f (tm_app s t) = tm_app (level_map f s) (level_map f t).
  Proof. unfold level_map. now tmv_simpl. Qed.

  Theorem level_map_abs f T t :
    level_map f (tm_abs T t) = tm_abs T (level_map f t).
  Proof. unfold level_map. now tmv_simpl. Qed.

  Theorem level_map_other f t :
    tm_other t -> level_map f t = t.
  Proof. intros. unfold level_map. now tmv_simpl. Qed.

  Hint Rewrite level_map_lvl level_map_app level_map_abs : tm.
  Hint Rewrite level_map_other using assumption : tm.

  Theorem level_map_f_eq f g t :
    (forall n, f n = g n) -> level_map f t = level_map g t.
  Proof.
    intros H. tm_induction t; tm_simpl; congruence.
  Qed.


  (** Apply "f" to all bound variables in the term "t" *)
  Definition bound_level_map f m :=
    level_map (fun n => if decide (m <= n) then f n else n).

  Notation lift := (bound_level_map S).

  Theorem has_type_bound_level_map1_h l m (c d : context) t T :
    l <= c -> rl_length d = m + c ->
    (forall n, n >= l -> n < c -> d (m + n) = c n) ->
    (forall n, n < l -> d n = c n) ->
    has_type c t T ->
    has_type d (bound_level_map (Nat.add m) l t) T.
  Proof.
    revert c d T. unfold bound_level_map.
    tm_induction t; intros c d A Hl L Hlg Hll HT; tm_simpl; has_type.
    - destruct (decide (l <= n)).
      + rewrite Hlg by easy. ltac1:(intuition lia).
      + rewrite Hll by lia. ltac1:(intuition lia).
    - eexists; eauto.
    - apply (IHt (c +: T)); try assumption; try (intros n Hn); simpl; try (lia).
      + destruct (decide (m + n < d)), (decide (n < c)); auto; intros; lia.
      + destruct (decide (n < d)), (decide (n < c)); auto; lia.
  Qed.

  Theorem has_type_bound_level_map2_h l m (c d : context) t T :
    l <= c -> rl_length d = m + c ->
    (forall n, n >= l -> n < c -> d (m + n) = c n) ->
    (forall n, n < l -> d n = c n) ->
    has_type d (bound_level_map (Nat.add m) l t) T ->
    has_type c t T.
  Proof.
    revert c d T. unfold bound_level_map.
    tm_induction t; intros c d A Hl L Hlg Hll HT; tm_simpl in *; has_type.
    - destruct (decide (l <= n)).
      + rewrite Hlg in E; ltac1:(intuition lia).
      + rewrite Hll in E; ltac1:(intuition lia).
    - eexists; eauto.
    - apply (IHt (c +: T) (d +: T)); try assumption;
        try (intros n Hn); simpl; try (lia).
      + destruct (decide (m + n < d)), (decide (n < c)); auto; intros; lia.
      + destruct (decide (n < d)), (decide (n < c)); auto; lia.
  Qed.

  Theorem has_type_bound_level_map1 m (c d : context) t T :
    rl_length d = m + c ->
    (forall n, n < c -> d n = c n) ->
    has_type c t T ->
    has_type d (bound_level_map (Nat.add m) c t) T.
  Proof.
    intros.
    eapply has_type_bound_level_map1_h; try eassumption; lia.
  Qed.

  Theorem has_type_lift1 {C c t T} :
    has_type C t T ->
    has_type (C +: c) (lift C t) T.
  Proof.
    intros Ht. apply (has_type_bound_level_map1 1); simpl; try (easy).
    intros. now rewrite decide_True.
  Qed.

  Theorem has_type_bound_level_map2 m (c d : context) t T :
    rl_length d = m + c ->
    (forall n, n < c -> d n = c n) ->
    has_type d (bound_level_map (Nat.add m) c t) T ->
    has_type c t T.
  Proof.
    intros. eapply has_type_bound_level_map2_h; try eassumption; lia.
  Qed.

  Theorem has_type_lift2 C c t T :
    has_type (C +: c) (lift C t) T -> has_type C t T.
  Proof.
    intros Ht.
    eapply (has_type_bound_level_map2 1); try eassumption; simpl; try (easy).
    intros. now rewrite decide_True.
  Qed.

  Theorem has_type_lift C c t T :
    has_type (C +: c) (lift C t) T <-> has_type C t T.
  Proof.
    split.
    - apply has_type_lift2.
    - apply has_type_lift1.
  Qed.

  Theorem bound_level_map_id m n t :
    ~ contains_bound_levels m n t ->
    bound_level_map (Nat.add n) m (bound_level_map (fun x => x - n) m t) = t.
  Proof.
    unfold bound_level_map, contains_bound_levels.
    intros L. tm_induction t; tm_simpl in *.
    - f_equal. (* There is a Coercion *)
      destruct (decide (m <= n0)), (decide (m <= n0 - n)); try lia.
      destruct (decide (m <= n0)); lia.
    - ltac1:(intuition congruence).
    - ltac1:(intuition congruence).
    - rewrite (level_map_other _ t) by assumption.
      now tm_simpl.
  Qed.

  Ltac2 htg_lift () := refine '(has_type_lift1 _).
  Ltac2 Set htg_list as old := fun () => List.append (old ()) [htg_lift].
  (*
  Ltac2 Set has_type_goal as old := fun () =>
    Control.plus old ( fun _ =>
      lazy_match! (Control.goal ()) with
      | has_type (?_c +: _) (lift (rl_length ?_c) _) _ => apply has_type_lift1
      end
    ).
    *)


  (********************)
  (** ** Substitution *)
  (********************)

  (** Parallel substitution *)
  Definition subst m l t :=
    (fix fx m l t :=
      match t with
      | tmv_lvl n => lookup_default (tm_lvl n) n l
      | tmv_app a b => tm_app (fx m l a) (fx m l b)
      | tmv_abs T t => tm_abs T (fx (S m) ((lift m <$> l) +: tm_lvl m) t)
      | tmv_other t => t
    end) m l (to_tmv t).

  Theorem subst_lvl m l n :
    subst m l (tm_lvl n) = lookup_default (tm_lvl n) n l.
  Proof. unfold subst. now tmv_simpl. Qed.

  Theorem subst_app m l s t :
    subst m l (tm_app s t) = tm_app (subst m l s) (subst m l t).
  Proof. unfold subst. now tmv_simpl. Qed.

  Theorem subst_abs m l T t :
    subst m l (tm_abs T t) = tm_abs T (subst (S m) ((lift m <$> l) +: tm_lvl m) t).
  Proof. unfold subst. now tmv_simpl. Qed.

  Theorem subst_other m l t : tm_other t -> subst m l t = t.
  Proof. intros. unfold subst. now tmv_simpl. Qed.

  Hint Rewrite subst_lvl subst_app subst_abs : tm.
  Hint Rewrite subst_other using easy : tm.


  Instance subst_Proper m : Proper ((≡) ==> (=) ==> (=)) (subst m).
  Proof.
    intros x y E ? t ->.
    revert m x y E.
    tm_induction t; intros m x y E; tm_simpl.
    - unfold lookup_default. destruct E. rewrite H in *.
      destruct (decide (n < y)); auto.
    - now erewrite IHt1, IHt2.
    - f_equal. apply IHt. now rewrite E.
    - reflexivity.
  Qed.

  Theorem has_type_subst1 C T R t r :
    rl_length r = rl_length R ->
    (forall n, n < r -> has_type C (r n) (R n)) ->
    has_type R t T -> has_type C (subst C r t) T.
  Proof.
    revert C T R r.
    tm_induction t; intros C A R r L F HT; tm_simpl; has_type.
    - unfold lookup_default.
      rewrite <- L in L0. subst. rewrite decide_True; auto.
    - eexists; eauto.
    - eapply IHt; try eassumption; simpl.
      + congruence.
      + intros. rewrite L. destruct (decide (n < R)); has_type.
        * apply F. congruence.
        * simpl. rewrite decide_False; ltac1:(intuition lia).
  Qed.

  Theorem has_type_subst2 (C R : context) T t r :
    C <= R -> rl_length r = R ->
    (forall n, n < r -> has_type C (r n) (R n)) ->
    has_type C (subst C r t) T -> has_type R t T.
  Proof.
    revert C T R r.
    tm_induction t; intros C A R r L E F HT.
    - assert (HT1 := HT). unfold subst in HT. tm_simpl in HT1.
      assert (Hn : exists A, has_type R n A). {
        destruct (decide (n < R)) as [Hn | Hn].
        - exists (R n). has_type. intuition.
        - unfold lookup_default in HT1.
          destruct (decide (n < r)); try (lia).
          has_type. ltac1:(intuition lia).
      }
      destruct Hn as [X H]. ltac1:(replace A with X) > [assumption|].
      eapply has_type_subst1 in H; try eassumption.
      eapply has_type_unique; eassumption.
    - tm_simpl in *. has_type.
      exists x; eauto.
    - tm_simpl in HT. has_type.
      eapply (IHt (C +: T)).
      4:{
        ltac1:(replace (S C) with (rl_length (C +: T)) in H) > [|reflexivity].
        apply H.
      }
      + simpl. lia.
      + simpl. congruence.
      + intros. simpl in *. rewrite E. destruct (decide (n < R)); has_type.
        * apply F. lia.
        * simpl. rewrite decide_False; ltac1:(intuition lia).
    - tm_simpl in *. now has_type.
  Qed.

  Theorem has_type_subst (C R : context) T t r :
    C <= R -> rl_length r = R ->
    (forall n, n < r -> has_type C (r n) (R n)) ->
    has_type C (subst C r t) T <-> has_type R t T.
  Proof.
    split; intros.
    - eapply has_type_subst2; eassumption.
    - eapply has_type_subst1; eassumption.
  Qed.


  Definition subst_last m n s := subst n (Build_rlist m tm_lvl +: s).

  Notation "[ n ; m | s ] t" := (subst_last n m s t)
    (in custom stlc_tm at level 5) : stlc_scope.
  Notation "[ n | s ] t" := (subst_last n n s t)
    (in custom stlc_tm at level 5) : stlc_scope.

  Theorem subst_last_app m n s a b :
    subst_last m n s (tm_app a b) =
    tm_app (subst_last m n s a) (subst_last m n s b).
  Proof. unfold subst_last. now tm_simpl. Qed.

  Theorem subst_last_other m n s t : tm_other t -> subst_last m n s t = t.
  Proof. intros. unfold subst_last. now tm_simpl. Qed.

  Hint Rewrite subst_last_app : tm.
  Hint Rewrite subst_last_other using easy : tm.


  Theorem has_type_subst_last1 (C D : context) T X s t :
    C <= D ->
    (forall n, n < C -> C n = D n) ->
    has_type D s T ->
    has_type (C +: T) t X -> has_type D (subst_last C D s t) X.
  Proof.
    intros ? E **. eapply has_type_subst1; try eassumption; try reflexivity.
    intros. simpl in *. destruct (decide (n < C)); try (easy).
    rewrite E by assumption. has_type. ltac1:(intuition lia).
  Qed.

  Theorem has_type_subst_last_s1 (C : context) T X s t :
    has_type C s T ->
    has_type (C +: T) t X -> has_type C (subst_last C C s t) X.
  Proof. intros. eapply has_type_subst_last1; eauto. Qed.

  Theorem has_type_subst_last2 (C D : context) T X s t :
    C <= D -> D <= S C ->
    (forall n, n < C -> C n = D n) ->
    has_type D s T ->
    has_type D (subst_last C D s t) X -> has_type (C +: T) t X.
  Proof.
    intros ? ? HD Hs Ht. eapply has_type_subst2; try eassumption; try reflexivity.
    intros. simpl in *. destruct (decide (n < C)); try (easy).
    rewrite HD by assumption. has_type. ltac1:(intuition lia).
  Qed.

  Theorem has_type_subst_last_s2 (C : context) T X s t :
    has_type C s T ->
    has_type C (subst_last C C s t) X ->
    has_type (C +: T) t X.
  Proof. intros. eapply has_type_subst_last2; eauto. Qed.


  (*****************)
  (** ** Reduction *)
  (*****************)

  Definition preserves_type (c : nat -> tm -> tm -> Prop) :=
    forall (C : context) T a b, c C a b ->
    has_type C a T -> has_type C b T.

  Inductive step c m : tm -> tm -> Prop :=
    | step_conv a b : c m a b -> step c m a b
    | step_appL a b t : step c m a b -> step c m (tm_app a t) (tm_app b t)
    | step_appR s a b : step c m a b -> step c m (tm_app s a) (tm_app s b)
    | step_abs T a b : step c (S m) a b -> step c m (tm_abs T a) (tm_abs T b).

  Definition reduces c m := rtc (step c m).
  Definition conv_eq c m := rtsc (step c m).

  Theorem has_type_step c (C : context) T a b :
    preserves_type c -> step c C a b ->
    has_type C a T -> has_type C b T.
  Proof.
    intros Hc BS. remember (rl_length C) as l.
    revert T. ltac1:(generalize dependent C).
    induction BS; intros C Hl A HT; has_type; eauto.
    - subst. unfold preserves_type in *. eauto.
    - apply IHBS.
      + simpl. lia.
      + assumption.
  Qed.


  Inductive beta_conv m : tm -> tm -> Prop :=
    beta_conv_intro T t s :
      beta_conv m (tm_app (tm_abs T t) s) (subst_last m m s t).

  Theorem has_type_beta_conv : preserves_type beta_conv.
  Proof.
    unfold preserves_type. intros * HB **.
    destruct HB. has_type.
    eapply has_type_subst_last1; try eassumption; easy.
  Qed.


  Inductive eta_conv m : tm -> tm -> Prop :=
    eta_conv_intro T t :
        ~ contains_bound_levels m 1 t ->
        eta_conv m (tm_abs T (tm_app t m)) (bound_level_map (fun x => x - 1) m t).

  Theorem has_type_eta_conv : preserves_type eta_conv.
  Proof.
    unfold preserves_type. intros * HE **.
    destruct HE. has_type. simpl in *.
    apply (has_type_bound_level_map2 1 _ (C +: T0)); try (easy).
    - intros. simpl. now rewrite decide_True.
    - rewrite bound_level_map_id; try (easy).
      rewrite decide_False in * by lia. ltac1:(intuition congruence).
  Qed.

  Definition lambda_equiv m :=
    conv_eq (fun m a b => beta_conv m a b \/ eta_conv m a b) m.
End StlcTheories.
