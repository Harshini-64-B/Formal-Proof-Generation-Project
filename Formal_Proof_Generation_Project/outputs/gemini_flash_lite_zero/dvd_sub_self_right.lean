theorem dvd_sub_self_right {n m : ℕ} : n ∣ m - n ↔ n ∣ m ∨ m ≤ n := by
  constructor
  · intro h
    by_cases hmn : m ≤ n
    · right; exact hmn
    · left
      push_neg at hmn
      have h1 : n ∣ (m - n) + n := dvd_add h (dvd_refl n)
      rw [Nat.sub_add_cancel (le_of_lt hmn)] at h1
      exact h1
  · intro h
    rcases h with h1 | h2
    · exact Nat.dvd_sub_of_dvd_right h1 (le_refl n)
    · rw [Nat.sub_eq_zero_of_le h2]
      exact dvd_zero n