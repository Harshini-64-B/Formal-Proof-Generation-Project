import Mathlib.Logic.Basic

namespace Logic_prop

theorem Iff.or {a c b d : Prop} (h₁ : a ↔ c) (h₂ : b ↔ d) : a ∨ b ↔ c ∨ d := by
  constructor
  . intro h
    simp_all
  . intro h
    simp_all

end Logic_prop
