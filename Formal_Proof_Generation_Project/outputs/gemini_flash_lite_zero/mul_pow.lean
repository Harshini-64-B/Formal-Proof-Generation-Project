theorem mul_pow {M : Type u_4} [CommMonoid M] (a b : M) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction' n with n ih
  · simp
  · rw [pow_succ, ih, pow_succ, pow_succ]
    -- (a * b) * (a ^ n * b ^ n) = (a * a ^ n) * (b * b ^ n) by associativity and commutativity
    calc
      (a * b) * (a ^ n * b ^ n) = a * (b * (a ^ n * b ^ n)) := by rw [mul_assoc]
      _ = a * ((b * a ^ n) * b ^ n) := by rw [mul_assoc]
      _ = a * ((a ^ n * b) * b ^ n) := by rw [← CommMonoid.mul_comm b (a ^ n)]
      _ = a * (a ^ n * (b * b ^ n)) := by rw [mul_assoc]
      _ = (a * a ^ n) * (b * b ^ n) := by rw [← mul_assoc]