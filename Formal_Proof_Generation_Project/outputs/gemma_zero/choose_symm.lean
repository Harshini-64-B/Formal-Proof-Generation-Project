theorem choose_symm {n k : ℕ} (hk : k ≤ n) : Nat.choose n (n - k) = Nat.choose n k := by
  rw [Nat.choose_subhk hk]