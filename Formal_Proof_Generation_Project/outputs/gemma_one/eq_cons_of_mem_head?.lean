theorem eq_cons_of_mem_head? {x : α} : ∀ {l : List α}, x ∈ l.head? → l = x :: l.tail := by
  intro l h
  cases l with
  | nil =>
    simp at h
    contradiction
  | cons a t =>
    simp at h
    rw [h]