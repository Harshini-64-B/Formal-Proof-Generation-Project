theorem div_right_comm (a b c : ℕ) : a / b / c = a / c / b := by
  by_cases hb : b = 0
  · by_cases hc : c = 0
    · simp
    · simp [hb]
  · by_cases hc : c = 0
    · simp [hc]
    · rw [Nat.div_div_eq_div_mul hb hc, Nat.div_div_eq_div_mul hc hb, Nat.mul_comm b c]