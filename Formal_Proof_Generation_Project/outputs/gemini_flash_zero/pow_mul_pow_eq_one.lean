theorem pow_mul_pow_eq_one {M : Type u_4} [Monoid M] {a b : M} (n : ℕ) : a * b = 1 → a ^ n * b ^ n = 1 := by
  intro h
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ a n, pow_succ' b n, ← mul_assoc (a ^ n * a), mul_assoc (a ^ n), h, mul_one, ih]