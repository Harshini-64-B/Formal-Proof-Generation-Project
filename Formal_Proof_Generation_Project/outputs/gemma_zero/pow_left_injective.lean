theorem pow_left_injective {n : Nat} (hn : n ≠ 0) : Function.Injective fun (a : Nat) => a ^ n := by
  intro a b hab
  by_contra h
  have h_lt : a < b ∨ b < a := Nat.lt_or_lt_of_ne_self hab h
  rcases h_lt with h_ab | h_ba
  · rw [← hab] at h_ab
    contradiction
  · rw [← hab] at h_ba
    contradiction