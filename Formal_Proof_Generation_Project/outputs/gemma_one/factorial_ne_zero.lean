theorem factorial_ne_zero (n : ℕ) : Nat.factorial n ≠ 0 := by
  induction n with
  | zero => simp [Nat.factorial_zero]
  | succ n ih =>
    rw [Nat.factorial_succ n]
    exact Nat.mul_ne_zero (Nat.succ_ne_zero n) ih