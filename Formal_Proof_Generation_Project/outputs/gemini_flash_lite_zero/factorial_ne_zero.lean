theorem factorial_ne_zero (n : ℕ) : Nat.factorial n ≠ 0 := by
  induction' n with n ih
  · simp [Nat.factorial]
  · simp [Nat.factorial]
    exact Nat.mul_ne_zero ih (by decide)