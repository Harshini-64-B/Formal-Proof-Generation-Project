theorem div_div_div_eq {α : Type u_1} [DivisionCommMonoid α] (a b c d : α) : a / b / (c / d) = a * d / (b * c) := by
  simp [div_eq_mul_inv, mul_inv, mul_comm, mul_left_comm, mul_assoc]