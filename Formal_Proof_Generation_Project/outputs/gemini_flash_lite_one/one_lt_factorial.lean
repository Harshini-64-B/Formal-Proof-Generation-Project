theorem one_lt_factorial : 1 < Nat.factorial n ↔ 1 < n := by
  cases n
  · simp
  · rename_i n
    cases n
    · simp
    · rename_i n
      simp [Nat.factorial_succ, Nat.factorial_pos]
      exact Nat.succ_le_of_lt (Nat.factorial_pos (n + 1))