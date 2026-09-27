theorem choose_succ_self (n : ℕ) : Nat.choose n (Nat.succ n) = 0 := by
  apply Nat.choose_gt
  exact Nat.lt_succ_self n