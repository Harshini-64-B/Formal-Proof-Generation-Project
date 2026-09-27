theorem choose_one_right (n : ℕ) : Nat.choose n 1 = n := by
  induction' n with n ih
  · rfl
  · rfl