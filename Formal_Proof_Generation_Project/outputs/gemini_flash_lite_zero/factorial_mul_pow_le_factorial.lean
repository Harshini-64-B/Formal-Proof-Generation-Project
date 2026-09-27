theorem factorial_mul_pow_le_factorial : ∀ {m n : ℕ}, Nat.factorial m * (m + 1) ^ n ≤ Nat.factorial (m + n) := by
  intro m n
  induction' n with n ih
  · simp
  · have h1 : m + n.succ = (m + n) + 1 := by omega
    rw [h1, Nat.factorial_succ, pow_succ]
    have h2 : m.factorial * (m + 1) ^ n * (m + 1) ≤ Nat.factorial (m + n) * (m + 1) := Nat.mul_le_mul_right (m + 1) ih
    linarith [h2]