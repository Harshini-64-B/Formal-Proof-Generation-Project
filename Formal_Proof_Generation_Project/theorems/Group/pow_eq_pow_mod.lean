import Mathlib.Algebra.Group.Basic

namespace Algebra_group

theorem pow_eq_pow_mod {M : Type u_4} [Monoid M] {a : M} {n : ℕ} (m : ℕ) (ha : a ^ n = 1) : a ^ m = a ^ (m % n) := by
  sorry

end Algebra_group
