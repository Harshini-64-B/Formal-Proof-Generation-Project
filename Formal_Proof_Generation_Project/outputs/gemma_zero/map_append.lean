theorem map_append {α β} (f : α → β) : ∀ {l₁ l₂ : List α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂ := by
  intro l₁ l₂
  induction l₁ with
  | nil => rfl
  | cons x xs ih => simp [ih]