theorem nat_choose_two (n : 0 < n) : Nat.choose n 2 = n * (n - 1) / 2 := by
  cases' n with n'
  · contradiction
  · change Nat.succ n' * (Nat.succ n' - 1) / 2 = Nat.succ n' * (Nat.succ n' - 1) / 2
    exact rfl