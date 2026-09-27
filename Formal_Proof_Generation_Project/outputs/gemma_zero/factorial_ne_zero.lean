theorem factorial_ne_zero (n : ℕ) : Nat.factorial n ≠ 0 := by
  induction n with
  | zero => simp [Nat.factorial]
  | succ n ih =>
    rw [Nat.factorial]
    exact Nat.mul_ne_zero (Nat.succ_pos n) ih