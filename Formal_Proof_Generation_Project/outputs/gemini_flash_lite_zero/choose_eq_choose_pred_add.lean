theorem choose_eq_choose_pred_add {n k : ℕ} (hn : 0 < n) (hk : 0 < k) : Nat.choose n k = Nat.choose (n - 1) (k - 1) + Nat.choose (n - 1) k := by
  cases n with
  | zero => contradiction
  | succ n =>
    cases k with
    | zero => contradiction
    | succ k =>
      exact (Nat.choose_succ_succ n k).symm