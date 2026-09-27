theorem mul_one_div {G : Type u_3} [DivInvMonoid G] (x y : G) : x * (1 / y) = x / y := by
  rw [one_div, ← div_eq_mul_inv]