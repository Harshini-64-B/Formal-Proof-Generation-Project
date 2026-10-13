theorem choose_zero_succ (k : ℕ) : Nat.choose 0 (Nat.succ k) = 0 := by
  exact Nat.choose_eq_zero_of_lt (Nat.succ_pos k)