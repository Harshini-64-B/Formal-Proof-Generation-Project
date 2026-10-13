theorem inv_unique {M : Type u_4} [CommMonoid M] {x y z : M} (hy : x * y = 1) (hz : x * z = 1) : y = z := by
  calc
    y = 1 * y := (one_mul y).symm
    _ = (x * z) * y := by rw [← hz]
    _ = (x * y) * z := by
      rw [mul_comm x z, mul_assoc, mul_comm z y, ← mul_assoc, mul_comm y z]
      exact mul_assoc x y z
    _ = 1 * z := by rw [hy]
    _ = z := one_mul z