theorem div_right_comm (a b c : Nat) : a / b / c = a / c / b := by
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm b c, ← Nat.div_div_eq_div_mul]