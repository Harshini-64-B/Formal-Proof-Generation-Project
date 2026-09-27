theorem choose_ne_zero {n k : ℕ} (h : k ≤ n) : n.choose k ≠ 0 := by
  exact Nat.ne_of_gt (Nat.choose_pos h)