theorem choose_succ_self (n : ℕ) : Nat.choose n (Nat.succ n) = 0 := by
  exact Nat.choose_gt_of_lt (Nat.lt_succ_self n)