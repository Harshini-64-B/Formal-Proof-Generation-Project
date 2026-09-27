theorem map_append {α β} (f : α → β) : ∀ {l₁ l₂ : List α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
  | [], _ => rfl
  | x :: xs, l₂ => congr_arg (f x :: ·) (map_append f)