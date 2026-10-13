theorem factorial_le {m n} (h : m ≤ n) : Nat.factorial m ≤ Nat.factorial n := by
  induction n with
  | zero =>
    simp [h]
  | succ n' ih =>
    intro h
    cases (Nat.le_cases h) with
    | inl h_lt =>
      have h_le : m ≤ n' := Nat.lt_le_iff.mp h_lt
      exact Nat.le_trans (ih h_le) (Nat.factorial_le_factorial_succ n')
    | inr h_eq =>
      rw [← h_eq]
      rfl