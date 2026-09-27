theorem ne_and_eq_iff_right {a b c : α} (h : b ≠ c) : a ≠ b ∧ a = c ↔ a = c :=
  ⟨fun h => h.2, fun h_ac => ⟨fun h_ab => h (h_ab.symm.trans h_ac), h_ac⟩⟩