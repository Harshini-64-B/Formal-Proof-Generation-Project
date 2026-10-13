theorem choose_one_right (n : ℕ) : Nat.choose n 1 = n := by
  cases n with
  | zero => rfl
  | succ n =>
    simp [Nat.choose]
    rw [Nat.factorial_succ, Nat.factorial_eq_one]
    rw [Nat.mul_div_cancel_left]
    · rfl
    · exact Nat.factorial_pos n