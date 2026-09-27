theorem pow_eq_pow_mod {M : Type u_4} [Monoid M] {a : M} {n : ℕ} (m : ℕ) (ha : a ^ n = 1) : a ^ m = a ^ (m % n) := by
  nth_rw 1 [← Nat.div_add_mod m n]
  rw [pow_add, mul_comm (m / n) n, pow_mul, ha, one_pow, one_mul]