theorem mul_pow {M : Type u_4} [CommMonoid M] (a b : M) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, mul_assoc, mul_comm, mul_assoc, mul_assoc, pow_succ, mul_comm, pow_succ]