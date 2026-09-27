import Mathlib.Logic.Basic
import LeanCopilot

namespace Logic_Prop
-- 1. If a and b are equivalent, then their negations are also equivalent.
theorem Iff.not {a b : Prop} (h : a ↔ b) : ¬a ↔ ¬b := by
  constructor
  · intro hna hb
    exact hna (h.mpr hb)
  · intro hnb ha
    exact hnb (h.mp ha)

-- 2. If a is false, then a is true if and only if a is true.
theorem not_imp_self {a : Prop} : ¬a → (a ↔ a) := by
  intro hna
  constructor
  . intro ha
    exact ha
  . intro ha
    exact ha

-- 3. If a is equivalent to ¬b, then ¬a is equivalent to b.
theorem Iff.not_left {a b : Prop} (h : a ↔ ¬b) : ¬a ↔ b := by
  constructor
  . exact not_imp_comm.mpr h.mpr
  . intro hb ha
    exact h.mp ha hb

-- 4. If negation of a is equivalent to b, then a is equivalent to negation of b.
theorem Iff.not_right {a b : Prop} (h : ¬a ↔ b) : a ↔ ¬b := by
  constructor
  . intro ha hb
    exact h.mpr hb ha
  . exact not_imp_comm.mpr h.mp

-- 5. If a = b is equivalent to c = d, then a ≠ b is equivalent to c ≠ d.
theorem Iff.ne {α β : Sort*} {a b : α} {c d : β} : (a = b ↔ c = d) → (a ≠ b ↔ c ≠ d) := by
  intro h
  constructor
  . intro h1 h2
    exact h1 (h.mpr h2)
  . intro h1 h2
    exact h1 (h.mp h2)

-- 6. If a is not false, then a is true.
theorem of_not_not {a : Prop} : ¬¬a → a := by
  intro h
  simp at h
  exact h

-- 7. If a does not imply b, then a is true.
theorem of_not_imp {a b : Prop} : ¬(a → b) → a := by
  intro h
  simp at h
  exact h.1

-- 8. a is equal to b if and only if it is not the case that a is not equal to b.
theorem not_ne_iff {α : Sort u_1} {a b : α} : ¬a ≠ b ↔ a = b := by
  constructor
  . intro h
    simp at h
    exact h
  . intro h h1
    contradiction

-- 9. The exclusive OR of not a and b is equivalent to a ↔ b.
theorem xor_not_left {a b : Prop} : Xor (¬a) b ↔ (a ↔ b) := by
  constructor
  . intro h
    simp at h
    exact h
  . intro h
    simp
    exact h

-- 10. The exclusive OR of a and not b is equivalent to a ↔ b.
theorem xor_not_right {a b : Prop} : Xor a ¬b ↔ (a ↔ b) :=  by
  constructor
  . intro h
    simp at h
    exact h
  . intro h
    simp
    exact h

-- 11. The exclusive OR of not a and not b is equivalent to the exclusive OR of a and b.
theorem xor_not_not {a b : Prop} : Xor (¬a) ¬b ↔ Xor a b := by
  constructor
  . intro h
    unfold Xor at h
    simp at h
    unfold Xor
    rw[or_comm] at h
    rw[and_comm, or_comm, and_comm, or_comm]
    exact h
  . intro h
    unfold Xor at h
    unfold Xor
    simp
    rw[and_comm, or_comm, and_comm]
    exact h

-- 12. If exactly one of a and b is true, then at least one of them is true, i.e., If a XOR b is true, then a or b is true.
theorem Xor.or {a b : Prop} (h : Xor a b) : a ∨ b := by
  unfold Xor at h
  rw[and_or_right, or_and_left, or_and_left] at h
  rw[and_assoc] at h
  exact h.1

-- 13. For any proposition p, either p is true or p is false, i.e., A proposition or its negation is always true.
theorem or_not {p : Prop} : p ∨ ¬p := by
  by_cases h : p
  . left
    exact h
  . right
    exact h

-- 14. If assuming that p is false leads to a contradiction, then p is true, i.e., If ¬p → False, then p is true.
theorem by_contradiction {p : Prop} : (¬p → False) → p := by
  intro h
  simp at h
  exact h

-- 15. If q follows whether p is true or false, then q is true.
theorem by_cases {p q : Prop} (hpq : p → q) (hnpq : ¬p → q) : q := by
  by_cases h : p
  . exact hpq h
  . exact hnpq h

-- 16. For any two elements x and y, either x is equal to y, or x is not equal to y.
theorem eq_or_ne {α : Sort u_1} (x y : α) : x = y ∨ x ≠ y := by
  by_cases h: x = y
  . left
    exact h
  . right
    exact h

-- 17. Equivalent propositions can be combined with AND to produce equivalent results, i.e., If a is equivalent to c and b is equivalent to d, then a ∧ b is equivalent to c ∧ d.
theorem Iff.and {a c b d : Prop} (h₁ : a ↔ c) (h₂ : b ↔ d) : a ∧ b ↔ c ∧ d := by
  constructor
  . simp_all
  . simp_all

-- 18. p is true and a is equal to b if and only if p is true and b is equal to a.
theorem and_symm_right {α : Sort u_1} (a b : α) (p : Prop) : p ∧ a = b ↔ p ∧ b = a := by
  constructor
  . intro h
    rw[eq_comm]
    exact h
  . intro h
    rw[eq_comm]
    exact h

-- 19. If a implies b is true, then either a is false or b is true.
theorem not_or_of_imp {a b : Prop} : (a → b) → ¬a ∨ b := by
  intro h
  by_cases h1 : b
  . right
    exact h1
  . left
    intro ha
    exact h1 (h ha)

-- 20. not a implies not b if and only if b implies a.
theorem not_imp_not {a b : Prop} : ¬a → ¬b ↔ b → a := by
  constructor
  . intro h hb
    by_cases h1 : a
    . exact h1
    . exact False.elim (h h1 hb)
  . intro h hna hnb
    exact hna (h hnb)

-- 21. p implies q and not p implies q if and only if q is true.
theorem imp_and_neg_imp_iff (p q : Prop) : (p → q) ∧ (¬p → q) ↔ q := by
  constructor
  . intro h
    simp at h
    exact h
  . intro h
    simp
    exact h

-- 22.a implies b if and only if a and b are not both true and false, respectively.
theorem not_and_not_right {a b : Prop} : ¬(a ∧ ¬b) ↔ a → b := by
  constructor
  . intro h ha
    simp at h
    exact h ha
  . intro h hne
    by_cases h1 : a
    . exact hne.2 (h h1)
    . exact h1 hne.1

-- 23. P XOR Q is false if and only if P and Q have the same truth value.
theorem not_xor (P Q : Prop) : ¬Xor P Q ↔ (P ↔ Q) := by
  constructor
  . intro h
    simp at h
    exact h
  . intro h
    simp
    exact h

-- 24. One of De Morgan's laws : The negation of a conjunction is logically equivalent to the disjunction of the negations
theorem not_and_or {a b : Prop} : ¬(a ∧ b) ↔ ¬a ∨ ¬b := by
  constructor
  . intro h
    by_cases ha : a
    . right
      intro hb
      exact h ⟨ha, hb⟩
    . left
      exact ha
  . intro h
    simp
    intro ha hb
    cases h with
    | inl h1 => contradiction
    | inr h1 => contradiction

-- 25. Two propositions a and b are equivalent if and only if they are equal.
theorem iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b) := by
  simp

-- 26. Equality is symmetric — saying “a equals b” is the same as saying “b equals a”.
theorem eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a) := by
  simp
  exact eq_comm

-- 27. For any propositions a and b, the statement a if and only if b is equivalent to b if and only if a.
theorem iff_comm_eq (a b : Prop) : (a ↔ b) = (b ↔ a) := by
  simp
  exact iff_comm

-- 28. For any b,c∈α, if every element a is equal to b exactly when it is equal to c, then b=c, and vice versa.
theorem eq_iff_eq_cancel_left {b c : α} : (∀ {a}, a = b ↔ a = c) ↔ b = c := by
  simp

-- 29. If b ≠ c, then a ≠ b and a=c if and only if a=c.
theorem ne_and_eq_iff_right {a b c : α} (h : b ≠ c) : a ≠ b ∧ a = c ↔ a = c := by
  constructor
  . intro h1
    exact h1.2
  . intro h1
    constructor
    . intro h2
      rw[h2] at h1
      exact h h1
    . exact h1

-- 30. The order of statements connected by “and” can be rearranged.
theorem And.rotate {a b c : Prop} : a ∧ b ∧ c → b ∧ c ∧ a := by
  intro h
  rw[and_comm, and_assoc] at h
  exact h

-- 31. If a implies b, then either b is true or a is false.
theorem or_not_of_imp : (a → b) → b ∨ ¬a := by
  intro h
  by_contra h'
  rw[not_or, not_not] at h'
  rcases h' with ⟨hb, hna⟩
  exact hb (h hna)

-- 32. If a implies either b or c, then either a implies b or a implies c, and vice versa.
theorem imp_or {a b c : Prop} : a → b ∨ c ↔ (a → b) ∨ (a → c) := by
  constructor
  . intro h
    by_cases ha : a = c
    · subst ha
      simp_all only [or_true, implies_true]
    · simp_all only [eq_iff_iff]
      apply Or.inl
      intro a_1
      simp_all only [forall_const, true_iff, or_false]
  . intro h h1
    simp_all only [forall_const]

-- 33. If a is equal to b, and b is different from c, then a is also different from c.
theorem ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ : b ≠ c) : a ≠ c := by
  intro h3
  rw[h₁] at h3
  contradiction


end Logic_Prop
