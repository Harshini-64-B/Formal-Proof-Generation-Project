theorem self_le_factorial : ∀ n : ℕ, n ≤ Nat.factorial n := by
  intro n
  induction' n with n ih
  · exact Nat.le_refl 1
  · cases' n with m
    · exact Nat.le_succ 1
    · have h1 : Nat.factorial (m.succ.succ) = (m.succ.succ) * Nat.factorial (m.succ) := rfl
      rw [h1]
      have h2 : m.succ ≤ Nat.factorial (m.succ) := ih
      have h3 : m.succ.succ ≥ 1 := Nat.succ_pos m.succ
      exact Nat.le_mul_of_pos_right h3 h2