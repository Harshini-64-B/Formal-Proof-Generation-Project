theorem pow_mul_pow_eq_one {M : Type u_4} [Monoid M] {a b : M} (n : ℕ) : a * b = 1 → a ^ n * b ^ n = 1 := by
  intro h
  induction' n with n ih
  · simp
  · rw [pow_succ, pow_succ]
    calc a * (a ^ n * (b ^ n * b)) = (a * a ^ n) * (b ^ n * b) := by rw [mul_assoc, ← mul_assoc (a ^ n), ← mul_assoc a, h, one_mul]
    _ = (a * a ^ n * b ^ n) * b := by rw [mul_assoc]
    _ = (a * (a ^ n * b ^ n)) * b := by rw [← mul_assoc]
    _ = (a * 1) * b := by rw [ih]
    _ = a * b := by rw [mul_one]
    _ = 1 := h