theorem nat_choose_two_self (n : ) : (n.choose 2) * 2 = n * (n - 1) := by
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp
    | succ n =>
      rw [Nat.choose_succ_succ]
      omega