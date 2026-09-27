theorem succ_injective : Function.Injective Nat.succ := by
  intro a b h
  exact Nat.succ.inj h