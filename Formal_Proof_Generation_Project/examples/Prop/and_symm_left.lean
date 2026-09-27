import Mathlib.Logic.Basic

namespace Logic_Prop

theorem and_symm_left {α : Sort u_1} (a b : α) (p : Prop) : a = b ∧ p ↔ b = a ∧ p := by
  constructor
  . intro h
    simp_all
  . intro h
    simp_all

end Logic_Prop
