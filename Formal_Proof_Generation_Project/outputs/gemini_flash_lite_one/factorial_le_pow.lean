theorem factorial_le_pow : ∀ n, Nat.factorial n ≤ n ^ n := by
  intro n
  induction' n with n ih
  · simp
  · calc Nat.factorial (n + 1)
      _ = (n + 1) * Nat.factorial n := by rfl
      _ ≤ (n + 1) * n ^ n := Nat.mul_le_mul_left (n + 1) ih
      _ ≤ (n + 1) * (n + 1) ^ n := Nat.mul_le_mul_left (n + 1) (Nat.pow_le_pow_left n.le_succ n)
      _ = (n + 1) ^ (n + 1) := by rw [pow_succ']