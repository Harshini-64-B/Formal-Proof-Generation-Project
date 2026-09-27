theorem mul_pow_sub_one {M : Type u_4} [Monoid M] {n : ℕ} (hn : n ≠ 0) (a : M) : a * a ^ (n - 1) = a ^ n := by
  cases n with
  | zero => contradiction
  | succ k =>
    rw [Nat.succ_sub_one, pow_succ]