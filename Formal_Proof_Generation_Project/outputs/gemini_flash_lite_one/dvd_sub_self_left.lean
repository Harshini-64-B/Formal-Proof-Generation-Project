theorem dvd_sub_self_left {n m : ℕ} : n ∣ n - m ↔ m = 0 ∨ n ≤ m := by
  constructor
  · intro h
    by_cases h2 : m = 0
    · left
      exact h2
    · right
      by_contra! h3
      have h4 : n - m < n := Nat.sub_lt (Nat.pos_of_ne_zero h2) h3
      have h5 : n - m = 0 := by
        rcases h with ⟨k, hk⟩
        cases k with
        | zero =>
          rw [Nat.mul_zero] at hk
          exact hk
        | succ k' =>
          have : n ≤ n - m := Nat.le_mul_of_pos_right n (Nat.succ_pos k')
          linarith
      linarith
  · intro h
    rcases h with rfl | h
    · rw [Nat.sub_zero]
      exact dvd_rfl
    · rw [Nat.sub_eq_zero_of_le h]
      exact dvd_zero n