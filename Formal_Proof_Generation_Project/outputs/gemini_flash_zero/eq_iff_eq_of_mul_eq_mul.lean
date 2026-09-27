theorem eq_iff_eq_of_mul_eq_mul {α : Type u_1} [CancelCommMonoid α] {a b c d : α} (h : a * b = c * d) : a = c ↔ b = d := by
  constructor
  · rintro rfl
    exact mul_left_cancel h
  · rintro rfl
    exact mul_right_cancel h