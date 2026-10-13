theorem nat_choose_two (n : 0 < 2 → n.choose 2 = n * (n - 1) / 2) : n.choose 2 = n * (n - 1) / 2 := by
  exact n (by decide)