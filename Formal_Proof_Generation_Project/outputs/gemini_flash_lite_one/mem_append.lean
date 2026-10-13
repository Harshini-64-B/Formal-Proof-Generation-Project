theorem mem_append {α} {a : α} {s t : List α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := by
  induction s with
  | nil =>
    simp
  | cons x xs ih =>
    simp [List.mem_cons, ih, or_assoc]