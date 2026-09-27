theorem neg_unique {M : Type u_4} [AddCommMonoid M] {x y z : M} (hy : x + y = 0) (hz : x + z = 0) : y = z := by
  rw [← add_zero y, ← hz, ← add_assoc, add_comm y, hy, zero_add]