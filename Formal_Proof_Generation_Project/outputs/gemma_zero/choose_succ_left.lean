by induction n with d hd
· simp [Nat.choose_zero, Nat.choose_zero, Nat.choose_one, Nat.choose_zero]
· rw [Nat.choose_succ, Nat.choose_succ, hd]
  simp [Nat.choose_succ, Nat.choose_succ, hd]