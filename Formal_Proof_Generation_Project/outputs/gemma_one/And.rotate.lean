theorem And.rotate {a b c : Prop} : a ∧ b ∧ c → b ∧ c ∧ a := by
  intro ⟨a, ⟨b, c⟩⟩
  exact ⟨b, ⟨c, a⟩⟩