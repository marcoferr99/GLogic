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
  - intros y [H1 H2]. constructor; [easy|].
    symmetry. apply H2. congruence.
  - intros y z [Hx1 Hx2] [Hy1 Hy2].
    constructor; [congruence|].
    intros. rewrite Hx2 by easy. rewrite Hy2; congruence.
Qed.

Instance rl_length_Proper {A} : Proper ((≡) ==> (=)) (@rl_length A).
Proof. now intros ? ? []. Qed.

Instance rlist_fmap_Proper {A B} : Proper ((=) ==> (≡) ==> (≡)) (rlist_fmap A B).
Proof.
  intros ? f -> x y [? H]. constructor; [easy|].
  intros. simpl in *. now rewrite H.
Qed.

Instance rl_cons_Proper {A} : Proper ((≡) ==> (=) ==> (≡)) (@rl_cons A).
Proof.
  intros ? ? [H ?] ? ? ->. constructor; simpl; [congruence|].
  intros. rewrite H in *. destruct (decide (n < y)); auto.
Qed.
