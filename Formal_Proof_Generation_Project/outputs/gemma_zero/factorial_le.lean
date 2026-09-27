theorem factorial_le {m n : Nat} (h : m ≤ n) : Nat.factorial m ≤ Nat.factorial n := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    cases Nat.le_cases h with
    | inl h_lt =>
      apply Nat.le_trans (ih (Nat.le_of_lt h_lt))
      apply Nat.le_mul_of_one_le
      · exact Nat.succ_pos n
      · exact Nat.factorial n
    | inr h_eq =>
      rw [h_eq]
      simp