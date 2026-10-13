theorem dvd_factorial : ∀ {m n}, 0 < m → m ≤ n → m ∣ Nat.factorial n := by
  intro m n hm hn
  induction n with
  | zero =>
    simp at hn hm
  | succ n ih =>
    cases lt_or_eq_of_le hn with
    | inl h_lt =>
      have h_le_n : m ≤ n := Nat.le_of_lt h_lt
      rw [Nat.factorial_succ n, Nat.mul_comm (n + 1) (Nat.factorial n)]
      exact Nat.dvd_mul_right (ih m hm h_le_n) (n + 1)
    | inr h_eq =>
      rw [h_eq, Nat.factorial_succ]
      exact Nat.dvd_mul_left (n + 1) (Nat.factorial n)