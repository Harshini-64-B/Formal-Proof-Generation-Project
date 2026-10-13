theorem mul_le_pow {a : ℕ} (ha : a ≠ 1) (b : ℕ) : a * b ≤ a ^ b := by
  by_cases ha0 : a = 0
  · rw [ha0]
    simp
  · have ha_ne_0 : a ≠ 0 := by
      intro h
      rw [h] at ha0
      contradiction
  · have ha_ge_2 : a ≥ 2 := by
      have h1 := Nat.ne_one_or_ge.mpr ha
      cases h1 with
      | inl h1_eq_1 => contradiction
      | inr h1_ge_2 => exact h1_ge_2
  · induction b with
    | zero => simp
    | succ b ih =>
      if hb : b = 0 then
        simp
      else
        have h_ih : a * (b + 1) ≤ a ^ b + a := Nat.add_le_add_left ih a
        have h_step : a ^ b + a ≤ a ^ b * a := by
          rw [← Nat.mul_add, ← Nat.add_succ, ← Nat.add_sub_left]
          apply Nat.add_le_add_left
          apply Nat.mul_le_mul_left
          · apply Nat.pow_ge
            exact ha_ge_2
            exact Nat.succ_pos b
          · exact Nat.sub_one_pos.mpr ha_ge_2
          exact a
        exact h_ih.trans h_step