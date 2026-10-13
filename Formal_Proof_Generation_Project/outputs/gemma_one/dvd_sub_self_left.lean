theorem dvd_sub_self_left {n m : ℕ} : n ∣ n - m ↔ m = 0 ∨ n ≤ m := by
  constructor
  · intro h
    rcases h with ⟨k, hk⟩
    by_cases hn : n = 0
    · simp [hn]
    · have h_pos : 0 < n := Nat.pos_of_ne_zero hn
      have h_le : n - m ≤ n := Nat.sub_le n m
      have hk_le : k ≤ 1 := Nat.le_of_mul_le_left h_pos h_le
      rcases hk_le with h0 | h1
      · rw [h0] at hk
        rw [Nat.sub_eq_zero_iff_le]
        exact hk
      · rw [h1] at hk
        rw [Nat.sub_eq_self_iff]
        left
        exact hk
  · intro h
    split
    · simp
    · simp [h]