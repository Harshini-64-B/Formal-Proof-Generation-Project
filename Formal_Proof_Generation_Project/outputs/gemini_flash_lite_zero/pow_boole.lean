theorem pow_boole {M : Type u_4} [Monoid M] (P : Prop) [Decidable P] (a : M) : (a ^ if P then 1 else 0) = if P then a else 1 := by
  split_ifs <;> simp