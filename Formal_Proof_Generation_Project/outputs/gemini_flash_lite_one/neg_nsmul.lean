theorem neg_nsmul {α : Type u_1} [SubtractionMonoid α] (a : α) (n : ℕ) : n • -a = -(n • a) := by
  induction' n with n ih
  · simp
  · rw [Nat.succ_nsmul, Nat.succ_nsmul, ih, neg_add]