theorem succ_injective : Function.Injective Nat.succ := by
  intro a b h
  injection h with h'
  exact h'