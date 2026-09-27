theorem pow_mul_pow_sub {M : Type u_4} [Monoid M] {m n : ℕ} (a : M) (h : m ≤ n) : a ^ m * a ^ (n - m) = a ^ n := by
  rw [← pow_add, Nat.add_sub_of_le h]