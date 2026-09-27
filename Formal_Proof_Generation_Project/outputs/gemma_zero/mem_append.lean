theorem mem_append {α} {a : α} {s t : List α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := by
  induction s with
  | nil => simp [List.append_nil]
  | cons x xs ih =>
    simp [List.append_cons]
    rw [ih]
    simp