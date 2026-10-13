theorem eq_cons_of_mem_head? {x : α} : ∀ {l : List α}, x ∈ l.head? → l = x :: l.tail := by
  intro l h
  cases l with
  | nil =>
    simp [List.head?] at h
  | cons hd tl =>
    simp [List.head?] at h
    subst h
    rfl