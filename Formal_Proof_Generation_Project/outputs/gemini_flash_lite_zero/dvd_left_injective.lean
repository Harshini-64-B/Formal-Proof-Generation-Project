theorem nat_choose_two_self (n : ) : (n.choose 2) * 2 = n * (n - 1) := by
  cases n with
  | zero => rfl
  | succ n_1 =>
    cases n_1 with
    | zero => rfl
    | succ n_2 =>
      rw [Nat.choose_succ_succ]
      omega