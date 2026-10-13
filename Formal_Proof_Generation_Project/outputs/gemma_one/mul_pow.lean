theorem mul_pow {M : Type u_4} [CommMonoid M] (a b : M) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, ih]
    simp [mul_assoc, mul_comm, pow_succ]