theorem ne_nil_of_length_pos {l : List α} (h: 0 < l.length) : l ≠ [] := by
  intro h_eq
  rw [h_eq, List.length_nil] at h
  contradiction