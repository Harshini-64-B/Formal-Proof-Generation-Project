theorem dvd_sub_self_right {n m : ℕ} : n ∣ m - n ↔ n ∣ m ∨ m ≤ n := by
  by_cases h : m ≤ n
  · simp [h, Nat.sub_eq_zero_of_le h]
  · push_neg at h
    simp [h]
    exact Nat.dvd_sub_self_right h