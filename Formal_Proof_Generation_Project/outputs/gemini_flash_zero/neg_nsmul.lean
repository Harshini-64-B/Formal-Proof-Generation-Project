theorem neg_nsmul {α : Type u_1} [SubtractionMonoid α] (a : α) (n : ℕ) : n • -a = -(n • a) := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, neg_zero]
  | succ n ih => rw [succ_nsmul, nsmul_succ, ih, neg_add_rev]