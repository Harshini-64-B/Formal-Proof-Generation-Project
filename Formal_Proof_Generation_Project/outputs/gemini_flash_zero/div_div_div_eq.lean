theorem div_div_div_eq {α : Type u_1} [DivisionCommMonoid α] (a b c d : α) : a / b / (c / d) = a * d / (b * c) := by
  rw [div_div_eq_mul_div, div_mul_eq_mul_div, div_div_eq_div_mul]