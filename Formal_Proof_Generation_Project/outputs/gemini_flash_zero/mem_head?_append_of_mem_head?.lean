theorem mem_head?_append_of_mem_head? {s t : List α} {x : α} (h : x ∈ s.head?) : x ∈ (s ++ t).head? := by
  cases s with
  | nil => cases h
  | cons y ys => exact h