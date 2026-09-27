import Mathlib.Logic.Basic

namespace Logic_Prop

theorem ne_of_ne_of_eq {α : Sort u_1} {a b c : α} (h₁ : a ≠ b) (h₂ : b = c) : a ≠ c := by
  intro h
  simp at h₁
  rw[h₂] at h₁
  exact h₁ h


end Logic_Prop
