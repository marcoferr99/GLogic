Require Export base.
From stdpp Require Export sets.


Ltac2 Notation "set_solver" := ltac1:(set_solver).
Ltac2 Notation "set_unfold" := ltac1:(set_unfold).

Theorem union_empty `{SemiSet T C} (X : C) : ∅ ∪ X ≡ X.
Proof. set_solver. Qed.

Theorem union_assoc `{SemiSet T C} (a b c : C) :
  a ∪ (b ∪ c) ≡ a ∪ b ∪ c.
Proof. set_solver. Qed.

