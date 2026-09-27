theorem factorial_mul_pow_le_factorial : ∀ {m n : ℕ}, Nat.factorial m * (m + 1) ^ n ≤ Nat.factorial (m + n) := by
  intro m n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.pow_succ]
    rw [Nat.mul_assoc]
    rw [Nat.factorial_succ (m + n)]
    apply Nat.mul_le_of_le_of_le
    · exact ih
    · exact Nat.le_add_right (m + 1) n