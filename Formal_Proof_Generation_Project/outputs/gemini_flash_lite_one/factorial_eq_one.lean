theorem factorial_eq_one : Nat.factorial n = 1 ↔ n ≤ 1 := by
  constructor
  · intro h
    rcases n with _ | n
    · contradiction
    · rcases n with _ | n
      · exact Nat.le_refl 1
      · exfalso
        have h2 : Nat.factorial (n.succ.succ) = (n.succ.succ) * Nat.factorial (n.succ) := rfl
        rw [h] at h2
        have h3 : 2 ≤ n.succ.succ := Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))
        have h4 : 2 * 1 ≤ (n.succ.succ) * Nat.factorial (n.succ) := by
          apply Nat.mul_le_mul h3
          rw [h]
        rw [← h2] at h4
        norm_num at h4
  · intro h
    rcases n with _ | n
    · rfl
    · rcases n with _ | n
      · rfl
      · contradiction