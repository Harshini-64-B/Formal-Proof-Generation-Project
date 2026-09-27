theorem choose_eq_zero_of_lt : ∀ {n k}, n < k → Nat.choose n k = 0 := by
  intro n k h
  simp [Nat.choose, h]