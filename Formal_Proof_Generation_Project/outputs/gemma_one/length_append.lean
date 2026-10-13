theorem length_append (l₁ l₂ : List α) : (l₁ ++ l₂).length = l₁.length + l₂.length := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih => simp [ih, Nat.add_assoc]