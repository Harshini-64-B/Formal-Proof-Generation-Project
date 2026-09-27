theorem mul_factorial_pred (n : ℕ) (hn : n ≠ 0) : n * Nat.factorial (n - 1) = Nat.factorial n := by
  cases n with
  | zero => contradiction
  | succ m => rw [Nat.factorial_succ, Nat.sub_succ]