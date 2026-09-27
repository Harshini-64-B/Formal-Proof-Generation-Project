theorem eq_cons_of_mem_head? {x : α} : ∀ {l : List α}, x ∈ l.head? → l = x :: l.tail := by
  intro l h
  cases l.head? with
  | none => contradiction
  | some y =>
    cases l with
    | nil => contradiction
    | cons y' t =>
      have h_eq : x = y' := by
        cases h
        congr
      rw [h_eq]
      rfl