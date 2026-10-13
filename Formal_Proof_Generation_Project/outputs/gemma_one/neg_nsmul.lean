theorem neg_nsmul {α : Type u_1} [SubtractionMonoid α] (a : α) (n : ℕ) : n • -a = -(n • a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [ih]
    have h : n • a + a = a + n • a := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [ih, add_assoc, add_assoc]
        rw [add_assoc]
    rw [← h, ← neg_add]