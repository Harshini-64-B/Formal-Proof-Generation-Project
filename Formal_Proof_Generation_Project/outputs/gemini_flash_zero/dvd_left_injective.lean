import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Basic

theorem dvd_left_injective : Function.Injective fun (x1 x2 : ℕ) => x1 ∣ x2 := by
  intro x1 x2 h
  have h1 : x2 ∣ x1 := by
    rw [← congr_fun h x1]
    exact dvd_rfl
  have h2 : x1 ∣ x2 := by
    rw [congr_fun h x2]
    exact dvd_rfl
  exact Nat.dvd_antisymm h2 h1