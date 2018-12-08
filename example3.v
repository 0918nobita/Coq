Definition fact : nat -> nat.
Proof.
  fix fact 1.
  intro x.
  case x.
  apply (S 0).
  intro y.
  apply (x * fact y).
Qed.

Eval compute in fact 2.
