import Mathlib.Data.Nat.Factorial.Basic

theorem dvd_factorial : ∀ {m n}, 0 < m → m ≤ n → m ∣ Nat.factorial n := by
  intro m n hm h
  induction n with
  | zero => omega
  | succ n ih =>
    rw [Nat.factorial_succ]
    rcases eq_or_lt_of_le h with rfl | hlt
    · exact dvd_mul_right (n + 1) (Nat.factorial n)
    · have h_le : m ≤ n := Nat.le_of_lt_succ hlt
      exact dvd_mul_of_dvd_right (ih h_le) (n + 1)