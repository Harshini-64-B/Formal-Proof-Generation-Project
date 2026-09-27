theorem div_mul_eq_div_mul_one_div {α : Type u_1} [DivisionCommMonoid α] (a b c : α) : a / (b * c) = a / b * (1 / c) := by
  rw [div_eq_mul_inv, mul_inv, ← mul_assoc, ← div_eq_mul_inv, ← one_div]