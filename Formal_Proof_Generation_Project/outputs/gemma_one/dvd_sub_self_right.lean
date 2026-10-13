theorem dvd_sub_self_right {n m : ℕ} : n ∣ m - n ↔ n ∣ m ∨ m ≤ n := by
  constructor
  · intro h
    by_cases h_lt : m < n
    · simp at h
      exact Or.inr (by simp [h_lt])
    · have h_m : n ∣ (m - n) + n := Nat.dvd_add h (Nat.dvd_of_self n)
      rw [Nat.sub_add_eq h_lt.not] at h_m
      exact Or.inl h_m
  · intro h
    by_cases h_lt : m < n
    · simp at h
      exact Or.inr (by simp [h_lt])
    · simp at h
      cases h with
      | inl h_dvd =>
        rw [Nat.sub_add_eq h_lt.not] at h_dvd
        exact (Nat.dvd_sub_of_dvd_add.mp h_dvd).1
      | inr h_le =>
        simp [h_le]
        exact Nat.dvd_zero _