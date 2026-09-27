theorem mul_pow_sub_one {M : Type u_4} [Monoid M] {n : ℕ} (hn : n ≠ 0) (a : M) : a * a ^ (n - 1) = a ^ n := by
  rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)]