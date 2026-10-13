theorem Iff.ne {α β : Sort*} {a b : α} {c d : β} : (a = b ↔ c = d) → (a ≠ b ↔ c ≠ d) := by
  intro h
  constructor
  · intro hab hcd
    apply hab
    exact (h.mp (not_congr h)).mpr hcd
  · intro hcd hab
    apply hcd
    exact (h.mpr (not_congr h)).mpr hab