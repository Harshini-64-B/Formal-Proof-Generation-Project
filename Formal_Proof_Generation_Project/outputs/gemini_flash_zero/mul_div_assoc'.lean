theorem mul_div_assoc' {G : Type u_3} [DivInvMonoid G] (a b c : G) : a * (b / c) = a * b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]