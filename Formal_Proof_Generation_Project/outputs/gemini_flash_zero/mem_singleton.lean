theorem mem_singleton (x a : α) : x ∈ [a] ↔ x = a := by
  constructor
  · intro h
    cases h with
    | head => rfl
    | tail _ h => cases h
  · rintro rfl
    exact List.Mem.head []