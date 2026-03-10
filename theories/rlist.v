From stdpp Require Export decidable.
From stdpp Require Import numbers.


Record rlist (A : Type) : Type := {
  rl_length :> nat;
  rl_map :> nat -> A
}.
Arguments Build_rlist {A}.
Arguments rl_length {A}.
Arguments rl_map {A}.

Declare Scope rlist_scope.
Delimit Scope rlist_scope with rlist.
Open Scope rlist_scope.


Definition lookup_default {A} d n (l : rlist A) : A :=
  if decide (n < l) then l n else d.

Definition rl_cons {A} (l : rlist A) a :=
  Build_rlist (S l) (fun n => if decide (n < l) then l n else a).

Notation "l +: e" := (rl_cons l e) (at level 50) : rlist_scope.

Instance rlist_fmap : FMap rlist :=
  fun _ _ f l => Build_rlist l (fun n => f (l n)).

(*
Theorem rlength_rcons : forall {A} (c : rlist A) t,
  rlength (rcons c t) = S (rlength c).
Proof.
  intros. unfold rcons. apply rlength_build_rlist.
Qed.

Theorem lookup_rcons_eq : forall {A} (c : rlist A) t n,
  n = rlength c -> rcons c t !! n = Some t.
Proof.
  intros.
  unfold rcons. rewrite lookup_build_rlist; [|lia].
  f_equal. rewrite decide_False; [easy|lia].
Qed.

Theorem lookup_rcons_lt : forall {A} (c : rlist A) t n,
  n < rlength c -> (c +: t) !! n = c !! n.
Proof.
  intros * H.
  unfold rcons. rewrite lookup_build_rlist; [|lia].
  apply is_Some_lookup in H as Hx. destruct Hx as [x Hx]. rewrite Hx.
  f_equal. rewrite decide_True; [|easy].
  unfold lookup_default. now rewrite Hx.
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

Instance rlist_lookup {A} : Lookup nat A (rlist A) := list_lookup.

Theorem is_Some_lookup {A} :
  forall (c : rlist A) n, is_Some (c !! n) <-> n < length c.
Proof. apply lookup_lt_is_Some. Qed.

Fixpoint build_rlist {A} n f : rlist A :=
  match n with
  | 0 => []
  | S n => build_rlist n f ++ [f n]
  end.

Theorem rlength_build_rlist : forall {A} n (f : nat -> A),
  length (build_rlist n f) = n.
Proof.
  intros. induction n; [reflexivity|].
  simpl. rewrite length_app. rewrite IHn. simpl. lia.
Qed.

Theorem lookup_build_rlist : forall {A} n (f : nat -> A) x,
  x < n -> build_rlist n f !! x = Some (f x).
Proof.
  intros. induction n; [lia|].
  simpl. destruct (decide (x = n)).
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
*)
