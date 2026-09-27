theorem pow_eq_pow_mod {M : Type u_4} [Monoid M] {a : M} {n : ℕ} (m : ℕ) (ha : a ^ n = 1) : a ^ m = a ^ (m % n) := by
  rw [← Nat.div_add_mod m n]
  rw [← pow_add]
  rw [← pow_mul_comm]
  rw [ha]
  rw [one_pow]
  rw [one_mul]