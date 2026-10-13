theorem boole_nsmul {M : Type u_4} [AddMonoid M] (P : Prop) [Decidable P] (a : M) : (if P then (1 : ℕ) else (0 : ℕ)) • a = if P then a else 0 := by
  by_cases h : P
  · simp [h]
  · simp [h]