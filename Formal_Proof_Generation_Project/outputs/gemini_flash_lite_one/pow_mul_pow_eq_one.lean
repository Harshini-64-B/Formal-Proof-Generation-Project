theorem pow_mul_pow_eq_one {M : Type u_4} [Monoid M] {a b : M} (n : ℕ) : a * b = 1 → a ^ n * b ^ n = 1 := by
  intro h
  induction' n with n ih
  · simp
  · calc a ^ (n + 1) * b ^ (n + 1) = a ^ n * a * (b * b ^ n) := by rw [pow_succ, pow_succ]
    _ = a ^ n * (a * b) * b ^ n := by group
    _ = a ^ n * 1 * b ^ n := by rw [h]
    _ = a ^ n * b ^ n := by rw [mul_one]
    _ = 1 := ih