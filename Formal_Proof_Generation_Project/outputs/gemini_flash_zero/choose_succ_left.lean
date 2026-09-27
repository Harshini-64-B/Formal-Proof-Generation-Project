theorem choose_succ_left (n k : ℕ) (hk : 0 < k) : Nat.choose (n + 1) k = Nat.choose n (k - 1) + Nat.choose n k := by
  cases k with
  | zero => cases hk
  | succ k => rw [Nat.choose_succ_succ]