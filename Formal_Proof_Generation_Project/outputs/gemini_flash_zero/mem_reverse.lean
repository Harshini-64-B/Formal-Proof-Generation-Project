theorem mem_reverse {α} {x : α} {l : List α} : x ∈ l.reverse ↔ x ∈ l := by
  induction l with
  | nil => simp
  | cons y ys ih => simp [ih, or_comm]