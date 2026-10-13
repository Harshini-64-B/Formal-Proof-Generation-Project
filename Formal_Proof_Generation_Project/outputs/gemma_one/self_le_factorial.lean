theorem self_le_factorial : ∀ n : ℕ, n ≤ Nat.factorial n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ]
    apply Nat.le_mul_left
    exact Nat.factorial_pos n