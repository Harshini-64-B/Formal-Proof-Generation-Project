theorem mul_factorial_pred (hn : n ≠ 0) : n * Nat.factorial (n - 1) = Nat.factorial n := by
  rw [Nat.factorial_succ (n - 1), Nat.sub_add_cancel n 1 hn]