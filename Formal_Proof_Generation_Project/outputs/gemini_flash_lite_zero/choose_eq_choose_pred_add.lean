theorem nat_choose_self_two (n : ) (h : n ≥ 2) : Nat.choose n 2 = n * (n - 1) / 2 := by
  have h2 : 2 ≤ n := h
  exact Nat.choose_two_right n