theorem cons_head?_tail : ∀ {l : List α} {a : α}, a ∈ l.head? → a :: l.tail = l := by
  intro l a h
  cases l with
  | nil =>
    simp [List.head?] at h
  | cons x xs =>
    simp [List.head?] at h
    rw [h]