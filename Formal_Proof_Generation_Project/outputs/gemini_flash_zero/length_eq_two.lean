theorem length_eq_two {l : List α} : l.length = 2 ↔ ∃ a b : α, l = [a, b] := by
  constructor
  · intro h
    match l with
    | [] => contradiction
    | [a] => contradiction
    | [a, b] => exact ⟨a, b, rfl⟩
    | a :: b :: c :: tl => contradiction
  · rintro ⟨a, b, rfl⟩
    rfl