theorem choose_succ_left (n k : ℕ) (hk : 0 < k) : Nat.choose (n + 1) k = Nat.choose n (k - 1) + Nat.choose n k := by
  have h : k = k - 1 + 1 := (Nat.sub_add_cancel hk).symm
  rw [h]
  exact Nat.choose_succ_succ n (k - 1)