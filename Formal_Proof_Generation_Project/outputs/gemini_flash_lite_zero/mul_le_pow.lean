theorem choose_three_succ (n : ) : Nat.choose (n + 1) 3 = Nat.choose n 3 + Nat.choose n 2 := by
  exact Nat.choose_succ_succ n 2