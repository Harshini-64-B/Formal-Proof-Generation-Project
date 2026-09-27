theorem div_mul_eq_div_mul_one_div {α : Type u_1} [DivisionCommMonoid α] (a b c : α) : a / (b * c) = a / b * (1 / c) := by
  rw [mul_inv_rev, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]