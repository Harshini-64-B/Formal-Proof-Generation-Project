theorem boole_nsmul {M : Type u_4} [AddMonoid M] (P : Prop) [Decidable P] (a : M) :
    (if P then 1 else 0) • a = if P then a else 0 := by
  split_ifs with h
  · rw [one_nsmul]
  · rw [zero_nsmul]