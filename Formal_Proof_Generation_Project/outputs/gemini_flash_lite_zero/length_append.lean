theorem length_append (l₁ l₂ : List α) : (l₁ ++ l₂).length = l₁.length + l₂.length := by
  induction l₁ with
  | nil => rfl
  | cons x xs ih =>
    simp [List.cons_append, ih, Nat.add_assoc]