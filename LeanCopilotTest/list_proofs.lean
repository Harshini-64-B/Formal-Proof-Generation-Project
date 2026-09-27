import Mathlib.Data.List.Basic
import LeanCopilot

-- 1. Length of an empty list - An empty list contains no elements. Therefore, its length is zero.
theorem length_nil: ([] : List α).length = 0 := by
  unfold List.length
  rfl

-- 2. Length of a cons list - A non-empty list consists of a head element and a tail list. Therefore, the length of the list is one more than the length of its tail.
theorem length_cons (a : α) (l : List α) : (a :: l).length = l.length + 1 := by
  unfold List.length
  split
  unfold List.length
  rfl     -- solves the first subgoal, i.e., l = [] case
  simp   -- solves the second subgoal, i.e., l = b :: l' case

-- 3. Left Identity of Append - Appending an empty list to the beginning of a list does not change the list.
theorem nil_append (l : List α) : [] ++ l = l := by
  simp

-- 4. Right Identity of Append - Appending an empty list to the end of a list does not change the list.
theorem append_nil (l : List α) : l ++ [] = l := by
  induction l with
  | nil => simp
  | cons a l ih => simp

-- 5. Length of an Appended List - When two lists are appended, the length of the resulting list is equal to the sum of the lengths of the two individual lists.
theorem length_append (l₁ l₂ : List α) : (l₁ ++ l₂).length = l₁.length + l₂.length := by
  induction l₁ with
  | nil => rw[List.nil_append, List.length_nil, Nat.zero_add]
  | cons a l₁ ih => rw[List.length_cons, Nat.add_assoc, Nat.add_comm 1, ← Nat.add_assoc]; simp [ih]

-- 6. Reverse of an Empty List - Reversing an empty list produces the empty list itself.
theorem reverse_nil : ([] : List α).reverse = [] := by
  unfold List.reverse
  unfold List.reverseAux
  rfl

-- 7. Reverse of a Singleton List - Reversing a singleton list returns the same list.
theorem reverse_singleton (a : α) : ([a] : List α).reverse = [a] := by
  unfold List.reverse
  unfold List.reverseAux
  unfold List.reverseAux
  rfl

-- 8. Membership in a Singleton List - An element belongs to the list if and only if it is equal to that single element.
theorem mem_singleton (x a : α) : x ∈ [a] ↔ x = a := by
  simp

-- 9. Empty List Has No Members - No element belongs to the empty list.
theorem not_mem_nil (x : α) : x ∉ [] := by
  intro h
  cases h

-- 10. Membership of the Head Element - The head element is always a member of the list.
theorem mem_cons_self (x : α) (l : List α) : x ∈ (x :: l) := by
  simp

-- 11. Reverse of a Reversed List - Reversing a list twice returns the original list.
theorem reverse_reverse {α} (l : List α) : l.reverse.reverse = l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

-- 12. Length of a Reversed List - Reversing a list does not change its length.
theorem length_reverse {α} (l : List α) : l.reverse.length = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

-- 13. Reverse Preserves Membership - Reversing a list does not change the elements it contains.
theorem mem_reverse {α} {x : α} {l : List α} : x ∈ l.reverse ↔ x ∈ l := by
  simp

-- 14. Mapping the Identity Function - Mapping the identity function over a list leaves the list unchanged.
theorem map_id {α} (l : List α) : List.map (id : α → α) l = l := by
  induction l with
  | nil => unfold List.map; rfl
  | cons a t ih => unfold List.map; rw[ih]; unfold id; rfl

-- 15. Length is Preserved by Map - Applying a function to every element of a list does not change its length.
theorem length_map {α β} (f : α → β) (l : List α) : (l.map f).length = l.length := by
  induction l with
  | nil => unfold List.map; rfl
  | cons a t ih => unfold List.map; rw[List.length_cons, List.length_cons, ih]

-- 16. Mapping Over an Empty List - Mapping any function over an empty list produces an empty list.
theorem map_nil {α β} (f : α → β) : List.map f [] = [] := by
  unfold List.map
  rfl

-- 17. Map Distributes Over Append - Mapping a function over two appended lists is the same as appending the mapped lists.
theorem map_append {α β} (f : α → β) : ∀ {l₁ l₂ : List α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; rw[List.nil_append, List.map_nil, List.nil_append]
  | cons a t ih => intro l₂; simp

-- 18. Taking Zero Elements - Taking (extracting) zero elements from any list produces the empty list.
theorem take_zero {α} (l : List α) : l.take 0 = [] := by
  unfold List.take
  rfl

-- 19. Dropping Zero Elements - Dropping zero elements from a list leaves the list unchanged.
theorem drop_zero {α} (l : List α) : l.drop 0 = l := by
  unfold List.drop
  rfl

-- 20. Taking the Length of a List - Taking as many elements as the length of a list returns the entire list.
theorem take_length {α} (l : List α) : l.take l.length = l := by
  induction l with
  | nil => unfold List.take; rfl
  | cons a t ih => unfold List.take; rw[ih]

-- 21. Dropping the Length of a List -Dropping as many elements as the length of a list results in the empty list.
theorem drop_length {α} (l : List α) : l.drop l.length = [] := by
  induction l with
  | nil => unfold List.drop; rfl
  | cons a t ih => unfold List.drop; rw[ih]

-- 22. Length of a Singleton List - A singleton list contains exactly one element.
theorem length_singleton {α} (a : α) : ([a] : List α).length = 1 := by
  unfold List.length
  rw[List.length_nil, Nat.zero_add]

-- 23. Cons is Never Equal to Nil - A non-empty list can never be equal to the empty list.
theorem cons_ne_nil {α} (a : α) (l : List α) : a :: l ≠ [] := by
  intro h
  cases h

-- 24. Tail of a Cons List - The tail of a non-empty list is the list obtained after removing its head.
theorem tail_cons {α} (a : α) (l : List α) : (a :: l).tail = l := by
  rfl

-- 25. Head of a Cons List - The head of a non-empty list is the first element of the list.
theorem head_cons {α} (a : α) (l : List α) {h} : (a :: l).head h = a := by
  rfl

-- 26. Head of an Empty List - An empty list has no head element.
theorem head?_nil {α} : ([] : List α).head? = none := by
  rfl

-- 27. Tail of an Empty List - The tail of an empty list is the empty list.
theorem tail_nil {α} : ([] : List α).tail = [] := by
  rfl

-- 28. Mapping Over a Singleton List - Mapping a function over a singleton list applies the function to the single element.
theorem map_singleton {α β} (f : α → β) (a : α) : List.map f [a] = [f a] := by
  unfold List.map
  rw[List.map_nil]

-- 29. Membership in an Appended List - An element belongs to the concatenation of two lists if and only if it belongs to at least one of the two lists.
theorem mem_append {α} {a : α} {s t : List α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := by
  constructor
  intro h
  cases s with
  | nil => rw[nil_append] at h; right; exact h
  | cons b s => simp at h; simp; rw[or_assoc]; exact h
  intro h
  simp
  exact h

-- 30.  If length of a list is positive, it is not empty.
theorem ne_nil_of_length_pos {l : List α} (h: 0 < l.length) : l ≠ [] := by
  intro h1
  rw[h1, List.length_nil] at h
  contradiction

-- 31. If a list is not empty, its length is positive.
theorem length_pos_of_ne_nil {l : List α} (h: l ≠ []) : 0 < l.length := by
  cases l with
  | nil => contradiction
  | cons a t => simp

-- 32. A list has a positive length iff it is not empty.
theorem length_pos_iff_ne_nil {l : List α} : l ≠ [] ↔ 0 < l.length := by
  constructor
  exact length_pos_of_ne_nil
  exact ne_nil_of_length_pos

-- 33. A list has successor length if and only if it can be written in head-and-tail form.
  theorem length_eq_succ_iff {n} {l : List α} : l.length = n + 1 ↔ ∃ a : α, ∃ t : List α, a :: t = l ∧ t.length = n := by
  constructor
  intro h
  cases l with
  | nil => rw[List.length_nil] at h; contradiction
  | cons a t => simp; simp at h; exact h
  intro h
  rcases h with ⟨a, t, h1, h2⟩
  rw[← h1, List.length_cons, h2]

-- 34. A list of length 2 is exactly of the form [a, b].
theorem length_eq_two {l : List α} : l.length = 2 ↔ ∃ a b : α, l = [a, b] := by
  constructor
  intro h
  cases l with
  | nil => simp at h
  | cons s t =>
        cases t with
        | nil => simp at h
        | cons p t' =>
            cases t' with
            | nil => refine ⟨s, p, ?_⟩ ; rfl
            | cons c t'' => simp at h
  rintro ⟨a, b, rfl⟩
  simp

-- 35. A list of length 3 is exactly of the form [a, b, c].
theorem length_eq_three {l : List α} : l.length = 3 ↔ ∃ a b c : α, l = [a, b, c] := by
  constructor
  intro h
  cases l with
  | nil => simp at h
  | cons s t =>
          cases t with
          | nil => simp at h
          | cons p t' =>
              cases t' with
              | nil => simp at h
              | cons q t'' =>
                  cases t'' with
                  | nil => refine ⟨s, p, q, rfl⟩
                  | cons r t1 => simp at h
  rintro ⟨a, b, c, rfl⟩
  simp

-- 36. A list of length 4 is exactly of the form [a, b, c, d].
theorem length_eq_four {l : List α} : l.length = 4 ↔ ∃ a b c d: α, l = [a, b, c, d] := by
  constructor
  intro h
  cases l with
  | nil => simp at h
  | cons s t =>
          cases t with
          | nil => simp at h
          | cons p t' =>
              cases t' with
              | nil => simp at h
              | cons q t'' =>
                  cases t'' with
                  | nil => simp at h
                  | cons r t1 =>
                      cases t1 with
                      | nil => refine ⟨s, p, q, r, rfl⟩
                      | cons m t2 => simp at  h
  rintro ⟨a,b,c,d,rfl⟩
  simp

-- 37.If an element is the head of a list, then the list can be represented as the cons of that element and the tail of the list.
theorem eq_cons_of_mem_head? {x : α} : ∀ {l : List α}, x ∈ l.head? → l = x :: l.tail := by
  intro l h1
  cases l with
  | nil => simp at h1
  | cons s t => simp at h1; simp; exact h1

-- 38. If a is the head of the list l, then adding a to the front of the tail of l reconstructs the original list.
theorem cons_head?_tail : ∀ {l : List α} {a : α}, a ∈ l.head? → a :: l.tail = l := by
  intro l a h
  cases l with
  | nil => simp at h
  | cons s t => simp at h; simp; symm; exact h

-- 39. The head of a non-empty list is its first element.
theorem head!_cons [Inhabited α] (a : α) (l : List α) : (a :: l).head! = a := by
  rfl

-- 40. The head of a non-empty list is an element of that list.
theorem head!_mem_self [Inhabited α] (l : List α) (h : l ≠ []) : l.head! ∈ l := by
  cases l with
  | nil => contradiction
  | cons s t => simp

-- 41. If l is a non-empty list, then prepending its head (head! l) to its tail (tail l) reconstructs the original list l.
theorem cons_head!_tail [Inhabited α] (l : List α) (h : l ≠ []) : l.head! :: l.tail = l := by
  cases l with
  | nil => contradiction
  | cons s t => simp

-- 42. If the first list is non-empty, then the head of the concatenation of two lists is the head of the first list.
theorem head?_append_of_ne_nil : ∀ (a : List α) {b : List α} (_ : a ≠ []), (a ++ b).head? = a.head? := by
  intro a b
  cases a with
  | nil => simp
  | cons s t => simp

-- 43. Appending two lists using List.append produces the same result as appending them using the notation ++.
theorem append_eq_has_append {a b : List α} : List.append a b = a ++ b := by
  rfl

-- 44. Appending a fixed list to the left of a list is an injective operation, i.e., If two lists become equal after appending the same prefix, then the original lists are equal.
-- theorem append_right_injective (s a b : List α) : s ++ a = s ++ b → a = b := by
--   intro h
--   simp at h
--   exact h
theorem append_right_injective (s : List α) : Function.Injective fun (t : List α) => s ++ t := by
  unfold Function.Injective
  intro a1 a2 h
  simp at h
  exact h

-- 45. Appending a fixed list to the right of a list is an injective operation, i.e., If two lists become equal after appending the same suffix, then the original lists are equal.
-- theorem append_left_injective (s a b : List α) : a ++ s = b ++ s → a = b := by
--   intro h
--   simp at h
--   exact h
theorem append_left_injective (t : List α) : Function.Injective fun (s : List α) => s ++ t := by
  unfold Function.Injective
  intro a1 a2 h
  simp at h
  exact h

-- 46. Replicating an element (m+n) times is the same as replicating it m times and appending it with replicating it n times.
theorem replicate_add (m n) (a : α) : List.replicate (m + n) a = List.replicate m a ++ List.replicate n a := by
  simp


-- 47. If you replicate an element a exactly n + 1 times, the resulting list is obtained by placing a at the front of a list consisting of n copies of a.
theorem replicate_succ {a : α} {n : Nat} : List.replicate (n + 1) a = a :: List.replicate n a := by
  simp [List.replicate]

-- 48.Appending a list to the end of a nonempty list does not change its head element, i.e., if x is the head element of a list s, then x is also the head element of s ++ t.
theorem mem_head?_append_of_mem_head? {s t : List α} {x : α} (h : x ∈ s.head?) : x ∈ (s ++ t).head? := by
  simp at h
  simp
  left
  exact h

-- 49. For a nonempty list, taking the tail after appending a single element is the same as taking the tail first and then appending that element.
theorem tail_append_singleton_of_ne_nil {a : α} {l : List α} (h : l ≠ []) : (l ++ [a]).tail = l.tail ++ [a] := by
  cases l with
  | nil => contradiction
  | cons s t => simp

-- 50. Looking up the element at position length of a list yields no element.
theorem getElem?_length (l : List α) : l[l.length]? = none := by
  cases l with
  | nil => simp
  | cons a t => simp


