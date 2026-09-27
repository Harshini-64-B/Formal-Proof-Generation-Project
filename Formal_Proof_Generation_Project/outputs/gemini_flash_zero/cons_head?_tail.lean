theorem cons_head?_tail : ∀ {l : List α} {a : α}, a ∈ l.head? → a :: l.tail = l := by
  intro l a h
  cases l with
  | nil => cases h
  | cons x xs =>
    cases h
    rfl