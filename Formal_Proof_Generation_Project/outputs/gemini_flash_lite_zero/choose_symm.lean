theorem nat_choose_self_two (n : ) : n.choose 2 = n * (n - 1) / 2 := by
  exact Nat.choose_two_right n