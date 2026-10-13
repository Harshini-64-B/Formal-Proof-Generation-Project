theorem ex_or_distrib (P Q R : Prop) : (P ∨ Q → R) ↔ (P → R) ∧ (Q → R) := by
  constructor
  · intro h
    constructor
    · intro p
      exact h (Or.inl p)
    · intro q
      exact h (Or.inr q)
  · intro h pqr
    rcases h with ⟨hp, hq⟩
    rcases pqr with p | q
    · exact hp p
    · exact hq q