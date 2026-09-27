theorem by_cases {p q : Prop} (hpq : p → q) (hnpq : ¬p → q) : q := by
  by_cases hp : p
  · exact hpq hp
  · exact hnpq hp