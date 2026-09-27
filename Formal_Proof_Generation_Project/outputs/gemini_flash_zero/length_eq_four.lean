theorem length_eq_four {l : List α} : l.length = 4 ↔ ∃ a b c d: α, l = [a, b, c, d] := by
  constructor
  · intro h
    match l with
    | [] => contradiction
    | [_] => contradiction
    | [_, _] => contradiction
    | [_, _, _] => contradiction
    | [a, b, c, d] => exact ⟨a, b, c, d, rfl⟩
    | _ :: _ :: _ :: _ :: _ => contradiction
  · rintro ⟨a, b, c, d, rfl⟩
    rfl