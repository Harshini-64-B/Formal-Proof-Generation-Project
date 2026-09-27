theorem dvd_sub_self_left {n m : ℕ} : n ∣ n - m ↔ m = 0 ∨ n ≤ m := by
  constructor
  · intro h
    by_contra h_not
    simp at h_not
    have h_m : m ≠ 0 := h_not.elim_right
    have h_n : n > m := h_not.elim_left
    rcases h with ⟨k, hk⟩
    have h_sub_lt : n - m < n := Nat.sub_lt h_n
    have h_k_pos : k ≠ 0 := by
      intro h0
      rw [h0] at hk
      exact Nat.sub_gt_zero h_n
    have h_k_ge_1 : k ≥ 1 := Nat.pos_iff_ge_one.mpr h_k_pos
    have h_n_le_nk : n ≤ n * k := Nat.mul_le_mul_left h_k_ge_1 n
    rw [hk] at h_sub_lt
    rw [h_n_le_nk] at h_sub_lt
    exact Nat.lt_irrefl n
  · intro h
    cases h <;> simp