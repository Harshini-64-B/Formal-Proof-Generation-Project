theorem choose_one_right (n : ℕ) : Nat.choose n 1 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_zero_right, ih]
    omega