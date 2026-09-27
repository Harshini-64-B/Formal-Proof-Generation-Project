theorem map_append {α β} (f : α → β) : ∀ {l₁ l₂ : List α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂
    rfl
  | cons x l₁ ih =>
    intro l₂
    simp [List.map, ih]