From Ltac2 Require Export Ltac2.

(** We use this scope for all notations in this project that do not belong to a
    more specific scope *)
Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.
