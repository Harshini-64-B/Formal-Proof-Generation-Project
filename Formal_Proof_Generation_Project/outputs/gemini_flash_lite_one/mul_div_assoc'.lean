theorem mul_div_assoc' {G : Type u_3} [DivInvMonoid G] (a b c : G) : a * (b / c) = a * b / c := by
  exact mul_div_assoc a b c