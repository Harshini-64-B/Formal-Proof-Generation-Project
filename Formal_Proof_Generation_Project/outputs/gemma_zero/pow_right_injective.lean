theorem pow_right_injective {a : ℕ} (ha : 2 ≤ a) : Function.Injective fun (x : ℕ) => a ^ x := by
  exact Function.StrictlyMonotone.injective (Nat.strict_mono_pow a ha)