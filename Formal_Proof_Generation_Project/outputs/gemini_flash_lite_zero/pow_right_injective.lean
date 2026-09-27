theorem pow_right_injective {a : ℕ} (ha : 2 ≤ a) : Function.Injective fun (x : ℕ) => a ^ x := by
  intro x y h
  have ha1 : 1 < a := lt_of_lt_of_le (by decide) ha
  exact Nat.pow_right_injective ha1 h