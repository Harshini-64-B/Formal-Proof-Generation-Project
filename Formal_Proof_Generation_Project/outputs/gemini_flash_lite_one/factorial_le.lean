theorem factorial_le {m n} (h : m ≤ n) : Nat.factorial m ≤ Nat.factorial n := by
  exact Nat.factorial_le_factorial h