theorem mul_rotate {G : Type u_3} [CommSemigroup G] (a b c : G) : a * b * c = b * c * a := by
  rw [mul_assoc, mul_comm a (b * c), ← mul_assoc]