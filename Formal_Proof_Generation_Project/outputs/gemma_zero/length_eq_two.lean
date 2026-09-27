theorem length_eq_two {l : List α} : l.length = 2 ↔ ∃ a b : α, l = [a, b] := by
  constructor
  · intro h
    cases l with
    | nil => contradiction
    | cons a as =>
      cases as with
      | nil => contradiction
      | cons b bss =>
        cases bss with
        | nil => exists_intro a (exists_intro b rfl)
        | cons c _ => contradiction
  · intro ⟨a, b, r⟩
    rw [r]
    rfl