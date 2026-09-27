theorem choose_eq_choose_pred_add {n k : ℕ} (hn : 0 < n) (hk : 0 < k) : Nat.choose n k = Nat.choose (n - 1) (k - 1) + Nat.choose (n - 1) k := by
  rw [← Nat.sub_add_cancel hn]
  rw [Nat.choose_succ_eq_add_choose hk]