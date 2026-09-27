theorem eq_cons_of_mem_head? {x : α} : ∀ {l : List α}, x ∈ l.head? → l = x :: l.tail := by
  intro l h
  cases l with
  | nil => contradiction
  | cons hd tl =>
    simp only [List.head?, List.mem_some, List.tail_cons] at h
    subst h
    rfl