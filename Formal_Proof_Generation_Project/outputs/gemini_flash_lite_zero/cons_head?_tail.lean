theorem cons_head?_tail : ∀ {l : List α} {a : α}, a ∈ l.head? → a :: l.tail = l := by
  intro l a h
  cases l with
  | nil => contradiction
  | cons x xs =>
    simp only [List.head?, List.mem_singleton] at h
    subst h
    rfl