theorem factorial_le_pow : ∀ n : ℕ, Nat.factorial n ≤ n ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.pow_succ]
    apply Nat.mul_le_mul_right
    · apply Nat.le_trans ih (Nat.pow_le_pow_left (Nat.le_succ n))
    · exact Nat.le_succ n