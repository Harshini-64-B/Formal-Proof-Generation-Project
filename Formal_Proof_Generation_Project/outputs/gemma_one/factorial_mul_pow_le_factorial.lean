theorem factorial_mul_pow_le_factorial : ∀ {m n : ℕ}, Nat.factorial m * (m + 1) ^ n ≤ Nat.factorial (m + n) := by
  intro m n
  induction n with
  | zero => simp
  | succ n ih =>
    calc Nat.factorial m * (m + 1) ^ (n + 1)
      = Nat.factorial m * (m + 1) ^ n * (m + 1) := by rw [Nat.pow_succ]
      _ ≤ Nat.factorial (m + n) * (m + 1) := by rw [ih]; exact Nat.mul_le_mul_left _ _
      _ ≤ Nat.factorial (m + n) * (m + n + 1) := by
        apply Nat.mul_le_mul_of_le_left
        exact Nat.add_le_add_left (Nat.add_le_add_right (Nat.zero_le n) 1) m
      _ = Nat.factorial (m + n + 1) := by rw [Nat.factorial_succ]