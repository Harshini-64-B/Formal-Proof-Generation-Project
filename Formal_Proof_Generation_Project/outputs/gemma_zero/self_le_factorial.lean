theorem self_le_factorial : ∀ n : ℕ, n ≤ Nat.factorial n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    simp [Nat.factorial]
    apply Nat.mul_le_mul_left
    · exact Nat.one_le_factorial n
    · exact Nat.mul_one (n + 1)