theorem mul_pow {M : Type u_4} [CommMonoid M] (a b : M) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction' n with n ih
  · simp
  · simp [pow_succ, ih]
    rw [mul_assoc, ← mul_assoc a, mul_comm a, mul_assoc]