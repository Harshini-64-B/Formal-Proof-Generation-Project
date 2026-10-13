theorem mem_reverse {α} {x : α} {l : List α} : x ∈ l.reverse ↔ x ∈ l := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp [List.reverse_cons]
    simp [List.mem_append, List.mem_singleton]
    rw [ih]
    rw [or_comm]
    rw [List.mem_cons]