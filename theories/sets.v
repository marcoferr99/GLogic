From stdpp Require Export sets.


Theorem union_empty `{SemiSet T C} (X : C) : ∅ ∪ X ≡ X.
Proof. set_solver. Qed.

Theorem union_assoc `{SemiSet T C} (a b c : C) :
  a ∪ (b ∪ c) ≡ a ∪ b ∪ c.
Proof. set_solver. Qed.

