Require Import stlc.


(*************************)
(** * G Logic Deductions *)
(*************************)

Record judgement : Set := {
  jd_signature : list ty;
  jd_formula : tm
}.

Record sequent : Set := {
  sq_context : list ty;
  sq_premises : list judgement;
  sq_conclusion : judgement
}.

Notation "|( sig ; l --> B )|" := (Build_sequent sig l B)
  (sig custom stlc_ty, l custom stlc_ty, B custom stlc_ty).
Notation "c :> t" := (Build_judgement c t)
  (in custom stlc_ty at level 60, t custom stlc_tm at level 50) : stlc_scope.

Check |( []; [] --> [] :> 0 )|.

Inductive def : sequent -> Prop :=
  | ax_init (sig : list ty) (j : judgement) (gam : list judgement) :
    def |( sig; j :: gam --> j )|
  | ax_cut (sig : list ty) (del gam : list judgement) (b c : judgement) :
    def |( sig; del --> b )| -> def |( sig; b :: gam --> c )| ->
    def |( sig; del ++ gam --> c )|
  | ax_cL (sig : list ty) (gam : list judgement) (b c : judgement) :
    def |( sig; b :: b :: gam --> c )| -> def |( sig; b :: gam --> c )|
  | ax_wL (sig : list ty) (gam : list judgement) (b c : judgement) :
    def |( sig; gam --> c )| -> def |( sig; b :: gam --> c )|
  | ax_botL
    (sig : list ty) (gam : list judgement) (b : judgement) (s : list ty) :
    def |( sig; (s :> _|) :: gam --> b)|
  | ax_topR
    (sig : list ty) (gam : list judgement) (s : list ty) :
    def |( sig; gam --> s :> ^| )|
.

Declare Custom Entry stlc_test.
Notation "x" := x (in custom stlc_test at level 0, x ident).

Notation "sig ; l --> B" := (Build_sequent sig l B) (at level 99, sig custom stlc_test at level 0).
Parameter sig : list ty.
Parameter l : list judgement.
Parameter B : judgement.
Check || [o;i] ; l --> B.

Notation "|( x )|" := x (x custom stlc_sequent) : stlc_scope.
Notation "x" := x (in custom stlc_sequent at level 0, x global) : stlc_scope.
Notation "( x )" := x (in custom stlc_sequent at level 0, x custom stlc_sequent) : stlc_scope.
Notation "sig ; l --> B" := (Build_sequent sig l B)
  (in custom stlc_sequent at level 99, sig custom stlc_ty at level 200, l custom stlc_sequent at level 200, B custom stlc_sequent at level 200, right associativity) : stlc_scope.

(** Examples *)
Parameter sig : list ty.
Parameter l : list judgement.
Parameter B : judgement.
Check |( sig ; l --> B )|.
Check |( []; [] --> [] :> 0 )|.


(* TODO: Verificare che B è una formula (cioè di tipo 'o') *)

Definition is_ax_init (c : sequent) (p : list sequent) :=
  p = [] /\ exists sig B gam, c = |(sig; B :: gam --> B)|.

Definition is_ax_cut (c : sequent) (p : list sequent) :=
  exists sig del gam B C,
  c = |(sig; del ++ gam --> C)| /\
  p = [|(sig; del --> B)|; |(sig; B :: gam --> C)|].

Definition is_ax_cL c p :=
  exists sig B gam C,
  p = [|(sig; B :: B :: gam --> C)|] /\
  c = |(sig; B :: gam --> C)|.

Definition is_ax_wL c p :=
  exists sig gam B C,
  p = [|(sig; gam --> C)|] /\
  c = |(sig; B :: gam --> C)|.
