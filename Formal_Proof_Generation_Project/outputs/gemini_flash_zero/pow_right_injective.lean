import Mathlib

theorem pow_right_injective {a : ℕ} (ha : 2 ≤ a) : Function.Injective fun (x : ℕ) => a ^ x :=
  (strictMono_pow_of_one_lt ha).injective