theorem mem_reverse {α} {x : α} {l : List α} : x ∈ l.reverse ↔ x ∈ l := by
  simp