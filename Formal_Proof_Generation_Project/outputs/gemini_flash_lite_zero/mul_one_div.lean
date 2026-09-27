theorem mul_one_div {G : Type u_3} [DivInvMonoid G] (x y : G) : x * (1 / y) = x / y := by
  exact mul_div_assoc x 1 y