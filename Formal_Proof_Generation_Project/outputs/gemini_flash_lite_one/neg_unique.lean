theorem neg_unique {M : Type u_4} [AddCommMonoid M] {x y z : M} (hy : x + y = 0) (hz : x + z = 0) : y = z := by
  calc y = 0 + y := by rw [zero_add]
    _ = (z + x) + y := by rw [← hz, add_comm]
    _ = z + (x + y) := by rw [add_assoc]
    _ = z + 0 := by rw [hy]
    _ = z := by rw [add_zero]