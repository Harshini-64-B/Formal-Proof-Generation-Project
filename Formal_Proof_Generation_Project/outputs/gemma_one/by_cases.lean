theorem by_cases {p q : Prop} (hpq : p → q) (hnpq : ¬p → q) : q := by
  by_cases h : p
  · exact hpq h
  · exact hnpq h