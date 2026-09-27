theorem pow_left_injective {n : Nat} (hn : n ≠ 0) : Function.Injective fun (a : Nat) => a ^ n := by
  intro a b h
  exact Nat.pow_left_cancel hn h