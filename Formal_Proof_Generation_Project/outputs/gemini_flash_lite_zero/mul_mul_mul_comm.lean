theorem mul_mul_mul_comm {G : Type u_3} [CommSemigroup G] (a b c d : G) : a * b * (c * d) = a * c * (b * d) := by
  rw [mul_assoc, mul_assoc, ← mul_assoc b, mul_comm b c, mul_assoc, ← mul_assoc]