theorem factorial_le_pow : ∀ n, Nat.factorial n ≤ n ^ n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.pow_succ]
    apply Nat.mul_le_mul_left
    apply Nat.le_trans ih
    apply Nat.pow_le_pow_of_le_right
    exact Nat.le_succ n