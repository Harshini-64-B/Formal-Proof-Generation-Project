theorem choose_succ_succ (n k : ℕ) : Nat.choose (Nat.succ n) (Nat.succ k) = Nat.choose n k + Nat.choose n (Nat.succ k) := by
  rw [Nat.choose_succ (Nat.succ_pos k), Nat.sub_succ, Nat.add_comm]