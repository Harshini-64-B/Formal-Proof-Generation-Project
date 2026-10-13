theorem mul_factorial_pred (hn : n ≠ 0) : n * Nat.factorial (n - 1) = Nat.factorial n := by
  cases n
  · contradiction
  · simp