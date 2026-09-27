theorem mem_head?_append_of_mem_head? {s t : List α} {x : α} (h : x ∈ s.head?) : x ∈ (s ++ t).head? := by
  cases s with
  | nil => contradiction
  | cons a s =>
    simp only [List.head?_cons] at h ⊢
    exact h