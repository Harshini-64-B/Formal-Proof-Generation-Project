theorem neg_nsmul {α : Type u_1} [SubtractionMonoid α] (a : α) (n : ℕ) : n • -a = -(n • a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [smul_succ, ih, neg_add]
    simp