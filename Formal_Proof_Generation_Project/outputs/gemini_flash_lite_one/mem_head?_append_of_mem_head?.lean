theorem mem_head?_append_of_mem_head? {s t : List α} {x : α} (h : x ∈ s.head?) : x ∈ (s ++ t).head? := by
  cases s with
  | nil =>
    simp [List.head?] at h
  | cons a l =>
    simp [List.head?] at h
    subst h
    simp [List.head?]