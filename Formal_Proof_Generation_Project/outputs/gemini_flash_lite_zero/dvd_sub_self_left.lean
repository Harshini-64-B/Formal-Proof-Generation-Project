theorem dvd_sub_self_left {n m : ℕ} : n ∣ n - m ↔ m = 0 ∨ n ≤ m := by
  constructor
  · intro h
    by_cases h2 : m = 0
    · left; exact h2
    · right
      by_contra! h3
      have h4 : n - m < n := Nat.sub_lt (Nat.pos_of_ne_zero h2) h3
      have h5 : n - m = 0 := Nat.eq_zero_of_dvd_of_lt h h4
      have h6 : n ≤ m := by
        exact Nat.le_of_sub_eq_zero h5
      exact h3 h6
  · rintro (rfl | h)
    · rw [Nat.sub_zero]
      exact dvd_refl n
    · rw [Nat.sub_eq_zero_of_le h]
      exact dvd_zero n