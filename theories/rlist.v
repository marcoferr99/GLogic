From stdpp Require Export decidable.
From stdpp Require Import numbers.


Record rlist (A : Type) : Type := {
  rl_length :> nat;
  rl_map :> nat -> A
}.
Arguments Build_rlist {A}.
Arguments rl_length {A}.
Arguments rl_map {A}.
Add Printing Constructor rlist.

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


Instance rlist_empty {A} `{Inhabited A} : Empty (rlist A) :=
  Build_rlist 0 inhabitant.

Inductive rlist_equiv {A} (l : rlist A) m : Prop :=
  rlist_equiv_intro : rl_length l = rl_length m ->
    (forall n, n < l -> l n = m n) ->
    rlist_equiv l m.

Instance rlist_Equiv {A} : Equiv (rlist A) := rlist_equiv.

Instance rlist_equiv_Equivalence A : Equivalence (@rlist_equiv A).
Proof.
  constructor; intros x.
  - now constructor.
  - intros y H. destruct H.
    constructor; [easy|].
    intros. symmetry. apply H0. congruence.
  - intros y z Hx Hz. destruct Hx, Hz.
    constructor; [congruence|].
    intros. rewrite H0; [rewrite H2|]; congruence.
Qed.

Instance rl_length_Proper {A} : Proper ((≡) ==> (=)) (@rl_length A).
Proof. intros x y E. now destruct E. Qed.

Instance rlist_fmap_Proper {A B} : Proper ((=) ==> (≡) ==> (≡)) (rlist_fmap A B).
Proof.
  intros ? f -> x y E. destruct E. constructor.
  - now simpl.
  - intros. simpl in *. now rewrite H0.
Qed.

Instance rl_cons_Proper {A} : Proper ((≡) ==> (=) ==> (≡)) (@rl_cons A).
Proof.
  intros x y E ? a ->. destruct E. constructor.
  - simpl. congruence.
  - intros. simpl in *. rewrite H in *. destruct (decide (n < y)); auto.
Qed.
