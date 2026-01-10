From Coq Require Import List.
Import ListNotations.


Inductive tree (A : Set) : Set :=
  node : A -> list (tree A) -> tree A.

Arguments node {A}.

Definition root {A} (t : tree A) : A :=
  match t with node a l => a end.


Notation deduction := tree.

Declare Custom Entry deduction.
Declare Scope deduction_scope.

Notation "<{ e }>" := e
  (e custom deduction at level 2) : deduction_scope.
Notation "p | c" := (node c p)
  (in custom deduction at level 90) : deduction_scope.
Notation "| c" := (node c [])
  (in custom deduction at level 90) : deduction_scope.
Notation "[ x ]" := (cons x nil)
  (in custom deduction at level 90) : deduction_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) (in custom deduction at level 90) : deduction_scope.
Notation "( x )" := x (in custom deduction) : deduction_scope.
Notation "x" := x
  (in custom deduction at level 0, x ident) : deduction_scope.

Open Scope deduction_scope.


Definition formal_system A := A -> list A -> Prop.

Inductive valid {A : Set} (S : formal_system A) : deduction A -> Prop :=
  is_valid a l : Forall (valid S) l -> S a (map root l) -> valid S (<{l | a}>).


(*******************************)
(** * Example: minimal Hilbert *)
(*******************************)

Inductive formula : Set :=
  | atomic : nat -> formula
  | implication : formula -> formula -> formula.

Infix "->" := implication (in custom deduction at level 50, right associativity) : deduction_scope.

Definition deduction_ex (A : formula) : deduction formula :=
  <{[[| (A -> (A -> A) -> A) -> (A -> A -> A) -> A -> A; | A -> (A -> A) -> A] | (A -> A -> A) -> A -> A; | A -> A -> A] | A -> A}>.

Definition is_kaxiom (f : formula) (p : list formula) : Prop :=
  p = [] /\ exists A B : formula, f = <{A -> B -> A}>.

Definition is_saxiom (f : formula) (p : list formula) : Prop :=
  p = [] /\ exists A B C : formula,
  f = <{(A -> (B -> C)) -> (A -> B) -> A -> C}>.

Definition is_mp (f : formula) (p : list formula) : Prop :=
  exists A B : formula, f = B /\ p = <{[A -> B; A]}>.

Definition h_system (c : formula) (p : list formula) : Prop :=
  is_kaxiom c p \/ is_saxiom c p \/ is_mp c p.

Theorem valid_ex : forall A, valid h_system (deduction_ex A).
Proof.
  intros.
  constructor.
  - constructor; constructor.
    + constructor; constructor; try apply Forall_nil.
      * right. left. constructor; try constructor.
        repeat eexists.
      * constructor; [constructor|].
        left. constructor; [constructor|].
        repeat eexists.
    + right. right. repeat eexists.
    + constructor; [constructor|].
      left. constructor; try constructor.
      repeat eexists.
    + constructor.
  - right. right. repeat eexists.
Qed.


(***********************************)
(** * Simply Typed Lambda Calculus *)
(***********************************)

Inductive ty : Set :=
  | ty_proposition : ty
  | ty_individual : ty
  | ty_arrow : ty -> ty -> ty.

(** Implementazione con indici di de Bruijn *)

Inductive tm : Set :=
  | tm_level : nat -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : ty -> tm -> tm.

(** Notations *)

Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.

Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.

Notation "x" := x (in custom stlc_ty at level 0, x global) : stlc_scope.

Notation "<{{ x }}>" := x (x custom stlc_ty).

Notation "( t )" := t (in custom stlc_ty at level 0, t custom stlc_ty) : stlc_scope.
Notation "A -> B" := (ty_arrow A B) (in custom stlc_ty at level 99, right associativity) : stlc_scope.

Notation "'o'" := ty_proposition (in custom stlc_ty at level 0) : stlc_scope.
Notation "'i'" := ty_individual (in custom stlc_ty at level 0) : stlc_scope.

Check <{{ o }}>.
Check <{{ o -> i }}>.
Check <{{ o -> (i -> o) }}>.
Check <{{ (o -> i) -> o }}>.


Notation "x" := x (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "({ x })" := x (x custom stlc_tm at level 200) : stlc_scope.
Notation "( t )" := t (in custom stlc_tm at level 0, t custom stlc_tm) : stlc_scope.
Notation "$( x )" := x (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.

Notation "x y" := (tm_app x y) (in custom stlc_tm at level 10, left associativity) : stlc_scope.
Notation "\: A , t" := (tm_abs A t) (in custom stlc_tm at level 200, A custom stlc_ty, t custom stlc_tm at level 200, left associativity).
Coercion tm_level : nat >-> tm.


Check ({ \: i, 1 }).
Check ({ \: (i -> i), 1}).
Check ({ (\: (i -> i), 2) 1}).


(********************)
(** ** Substitution *)
(********************)

Fixpoint incr (t : tm) : tm :=
  match t with
  | tm_level n => tm_level (S n)
  | tm_app t1 t2 => tm_app (incr t1) (incr t2)
  | tm_abs T t1 => tm_abs T (incr t1)
  end.

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc_tm at level 5, x constr, s custom stlc_tm, t custom stlc_tm at next level, right associativity).

Fixpoint subst (x : nat) (s : tm) (t : tm) : tm :=
  match t with
  | tm_level n => if Nat.eqb n x then s else t
  | ({t1 t2}) => ({[x:=s]t1 [x:=s]t2})
  | ({\: T, t1}) => ({\: T, [x+1:=$(incr s)]t1})
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc_tm).


Compute ({[1 := (\: i, 5)] (1 2)}).
Compute ({[0 := (\: i, 1 2)] (\: o, 1)}).
Compute ({[0 := (\: i, 1 2)] (\: o, \: i, 2 2)}).


(******************************)
(** * Intuitionistic sequents *)
(******************************)

Section section.
  Variable variable : Set.
  Variable formula : Set.

  Definition signature := list variable.

  Record judgement : Set := {
    _ : formula;
    _ : signature
  }.

  Record sequent : Set := {
    context : signature;
    premises : list judgement;
    conclusion : judgement
  }.

  Notation "sig , l --> j" := (Build_sequent sig l j) (at level 60).

  Notation deduction := (deduction sequent).

  Definition is_ax_init (c : sequent) (p : list sequent) :=
    p = [] /\ exists sig B gam, c = sig, B :: gam --> B.

  Definition is_ax_cut (c : sequent) (p : list sequent) :=
    exists sig del gam B C,
    c = sig, del ++ gam --> C /\
    p = [sig, del --> B; sig, B :: gam --> C].

  Definition is_ax_cL c p :=
    exists sig B gam C,
    p = [sig, B :: B :: gam --> C] /\
    c = sig, B :: gam --> C.

  Definition is_ax_wL c p :=
    exists sig gam B C,
    p = [sig, gam --> C] /\
    c = sig, B :: gam --> C.

  Definition is_ax_botL c p :=
End section.
