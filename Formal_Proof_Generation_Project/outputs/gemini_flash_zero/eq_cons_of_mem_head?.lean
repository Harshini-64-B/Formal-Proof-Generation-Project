theorem eq_cons_of_mem_head? {x : α} : ∀ {l : List α}, x ∈ l.head? → l = x :: l.tail
  | [], h => by cases h
  | y :: ys, h => by
    cases h
    rfl