theorem pow_right_injective {a : ℕ} (ha : 2 ≤ a) : Function.Injective fun (x : ℕ) => a ^ x := by
  intro x y h
  exact (Nat.pow_right_inj ha).mp h