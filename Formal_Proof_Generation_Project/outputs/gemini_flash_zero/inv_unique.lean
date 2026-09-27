theorem inv_unique {M : Type u_4} [CommMonoid M] {x y z : M} (hy : x * y = 1) (hz : x * z = 1) : y = z := by
  rw [← mul_one y, ← hz, ← mul_assoc, mul_comm y, hy, one_mul]