theorem pow_eq_pow_mod {M : Type u_4} [Monoid M] {a : M} {n : ℕ} (m : ℕ) (ha : a ^ n = 1) : a ^ m = a ^ (m % n) := by
  rw [Nat.div_add_mod m n, pow_add]
  have h1 : a ^ (n * (m / n)) = (a ^ n) ^ (m / n) := by
    rw [pow_mul]
  rw [h1, ha, one_pow, one_mul]