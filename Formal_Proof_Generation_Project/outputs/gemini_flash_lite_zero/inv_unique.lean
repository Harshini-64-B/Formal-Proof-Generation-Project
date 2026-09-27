theorem inv_unique {M : Type u_4} [CommMonoid M] {x y z : M} (hy : x * y = 1) (hz : x * z = 1) : y = z := by
  calc
    y = 1 * y := (one_mul y).symm
    _ = (x * z) * y := by rw [← hz]
    _ = (z * x) * y := by rw [mul_comm x z]
    _ = z * (x * y) := mul_assoc z x y
    _ = z * 1 := by rw [hy]
    _ = z := mul_one z