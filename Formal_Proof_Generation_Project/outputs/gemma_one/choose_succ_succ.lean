theorem choose_succ_succ (n k : ℕ) : Nat.choose (Nat.succ n) (Nat.succ k) = Nat.choose n k + Nat.choose n (Nat.succ k) := by
  rw [Nat.choose_succ_add_choose n (Nat.succ k) (Nat.succ_pos k)]
  rw [Nat.sub_succ]
  rw [Nat.add_comm]