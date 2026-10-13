theorem choose_two_eq_factorial_div (n : Nat) : n.choose 2 = n * (n - 1) / 2 := by
  rw [Nat.choose_two_right]