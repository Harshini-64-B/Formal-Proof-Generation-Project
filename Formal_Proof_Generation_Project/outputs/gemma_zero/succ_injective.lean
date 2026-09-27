theorem succ_injective : Function.Injective Nat.succ := by
  intro n m h
  injection h