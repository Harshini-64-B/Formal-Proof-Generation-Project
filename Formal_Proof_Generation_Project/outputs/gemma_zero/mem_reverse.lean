theorem mem_reverse {α} {x : α} {l : List α} : x ∈ l.reverse ↔ x ∈ l := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [List.reverse]
    constructor
    · intro hx
      cases hx <;> simp [ih]
    · intro hx
      cases hx <;> simp [ih]