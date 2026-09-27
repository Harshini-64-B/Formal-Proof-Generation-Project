theorem And.rotate {a b c : Prop} : a ∧ b ∧ c → b ∧ c ∧ a := by
  intro h
  rcases h with ⟨ha, hb, hc⟩
  exact ⟨hb, hc, ha⟩