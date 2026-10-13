theorem div_div_div_eq {α : Type u_1} [DivisionCommMonoid α] (a b c d : α) : a / b / (c / d) = a * d / (b * c) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, inv_div, mul_assoc]
  rw [div_eq_mul_inv, inv_mul]
  ring