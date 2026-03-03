From stdpp Require Export option.
Require Export base.
From stdpp Require Import list.

Export Nat Lia.


(** ** Reverse list interface *)

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


(** ** Reverse list theories *)

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


(** ** Reverse list implementation *)

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
