theorem dvd_sub_self_right {n m : ℕ} : n ∣ m - n ↔ n ∣ m ∨ m ≤ n := by
  constructor
  · intro h
    by_cases h_le : m ≤ n
    · left; exact h_le
    · right
      have h_gt : m > n := Nat.lt_of_not_le h_le.not
      rcases h with ⟨k, hk⟩
      rw [← dvd_def] at hk
      rw [Nat.sub_add_right h_gt] at hk
      rw [Nat.mul_add] at hk
      exact ⟨k + 1, hk⟩
  · intro h
    by_cases h_le : m ≤ n
    · rw [Nat.sub_eq_zero_of_le h_le]
      exact dvd_zero n
    · rcases h with ⟨h_m, h_gt⟩ | h_le_alt
      · rcases h_m with ⟨k, hk⟩
        have h_m_gt_n : m > n := Nat.lt_of_not_le h_le.not
        rw [← dvd_def]
        rw [Nat.sub_add_right h_m_gt_n] at hk
        rw [Nat.mul_add] at hk
        exact ⟨k, hk⟩
      · contradiction