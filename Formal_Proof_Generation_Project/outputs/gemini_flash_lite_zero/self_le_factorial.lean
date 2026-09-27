theorem self_le_factorial : ∀ n : ℕ, n ≤ Nat.factorial n := by
  intro n
  induction' n with n ih
  · simp
  · cases' n with m
    · simp
    · have h1 : m.succ ≤ Nat.factorial m.succ := by
        exact Nat.le_trans ih (Nat.le_mul_of_pos_right (Nat.factorial m.succ) (by omega))
      exact h1