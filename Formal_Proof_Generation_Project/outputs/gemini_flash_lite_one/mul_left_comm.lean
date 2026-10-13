theorem mul_left_comm {G : Type u_3} [CommSemigroup G] (a b c : G) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a b, mul_assoc]