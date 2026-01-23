Require Import stlc.


(*************************)
(** * G Logic Deductions *)
(*************************)

Module GLogic (Ty : TY).
  Module Stlc := Stlc Ty.
  Import Stlc.

  Record judgement : Set := {
    jd_context : context;
    jd_tm : tm
  }.

  Record sequent : Set := {
    sq_context : context;
    sq_premises : list judgement;
    sq_conclusion : judgement
  }.

  Notation "|( sig ; l --> B )|" := (Build_sequent sig l B)
    (sig custom stlc_ty, l custom stlc_ty, B custom stlc_ty).
  Notation "c :> t" := (Build_judgement c t)
    (at level 70, t custom stlc_tm at level 60) : stlc_scope.

  Inductive is_derivable : sequent -> Prop :=
    | rl_init C c t :
        has_type (C ++ c) t ty_prp ->
        is_derivable (Build_sequent C [c :> t] (c :> t))
    | rl_cut C l m b c :
        is_derivable (Build_sequent C l b) ->
        is_derivable (Build_sequent C (b :: m) c) ->
        is_derivable (Build_sequent C (l ++ m) c)
    | rl_cL C l b c :
        is_derivable (Build_sequent C (b :: b :: l) c) ->
        is_derivable (Build_sequent C (b :: l) c)
    | rl_wL C c l b t :
        has_type (C ++ c) t ty_prp ->
        is_derivable (Build_sequent C l b) ->
        is_derivable (Build_sequent C (c :> t :: l) b)
    | rl_botL C c d t :
        has_type (C ++ c) t ty_prp ->
        is_derivable (Build_sequent C [d :> tm_bot] (c :> t))
    | rl_topR C c :
        is_derivable (Build_sequent C [] (c :> tm_top))
    | rl_andL1 C c l b t s :
        has_type (C ++ c) t ty_prp ->
        is_derivable (Build_sequent C (c :> s :: l) b) ->
        is_derivable (Build_sequent C (c :> (tm_and s t) :: l) b)
    | rl_andL2 C c l b t s :
        has_type (C ++ c) s ty_prp ->
        is_derivable (Build_sequent C (c :> t :: l) b) ->
        is_derivable (Build_sequent C (c :> (tm_and s t) :: l) b)
    | rl_andR C c l t s :
        is_derivable (Build_sequent C l (c :> s)) ->
        is_derivable (Build_sequent C l (c :> t)) ->
        is_derivable (Build_sequent C l (c :> tm_and s t))
    | rl_orL C c l b t s :
        is_derivable (Build_sequent C (c :> s :: l) b) ->
        is_derivable (Build_sequent C (c :> t :: l) b) ->
        is_derivable (Build_sequent C (c :> tm_or s t :: l) b)
    | rl_orR1 C c l t s :
        has_type (C ++ c) t ty_prp ->
        is_derivable (Build_sequent C l (c :> s)) ->
        is_derivable (Build_sequent C l (c :> tm_or s t))
    | rl_orR2 C c l t s :
        has_type (C ++ c) s ty_prp ->
        is_derivable (Build_sequent C l (c :> t)) ->
        is_derivable (Build_sequent C l (c :> tm_or s t))
  .
End GLogic.
