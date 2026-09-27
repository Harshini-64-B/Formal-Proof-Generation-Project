theorem neg_unique {M : Type u_4} [AddCommMonoid M] {x y z : M} (hy : x + y = 0) (hz : x + z = 0) : y = z := by
  calc
    y = 0 + y := (zero_add y).symm
    _ = (x + z) + y := by rw [hz]
    _ = (z + x) + y := by rw [add_comm x z]
    _ = z + (x + y) := by rw [add_assoc]
    _ = z + 0 := by rw [hy]
    _ = z := add_zero z