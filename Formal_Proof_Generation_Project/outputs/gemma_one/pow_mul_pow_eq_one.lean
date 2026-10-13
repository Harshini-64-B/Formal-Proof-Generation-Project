theorem pow_mul_pow_eq_one {M : Type u_4} [Monoid M] {a b : M} (n : ℕ) : a * b = 1 → a ^ n * b ^ n = 1 := by
  intro h
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ_left, mul_assoc, mul_assoc, h, one_mul, ih]