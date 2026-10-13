theorem choose_symm {n k : ℕ} (hk : k ≤ n) : Nat.choose n (n - k) = Nat.choose n k := by
  exact Nat.choose_sub_eq_choose hk