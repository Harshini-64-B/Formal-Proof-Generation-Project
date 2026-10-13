theorem neg_unique {M : Type u_4} [AddCommMonoid M] {x y z : M} (hy : x + y = 0) (hz : x + z = 0) : y = z := by
  calc
    y = 0 + y := by rw [add_left_zero]
    _ = (x + z) + y := by rw [hz]
    _ = x + (z + y) := add_assoc x z y
    _ = x + (y + z) := add_comm z y
    _ = (x + y) + z := add_assoc x y z
    _ = 0 + z := by rw [hy]
    _ = z := add_left_zero z