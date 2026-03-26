/-
  Proving that an imperative max-finding algorithm satisfies:
    ∃ max ∈ s, ∀ x ∈ s, x ≤ max
-/

-- Models the loop body: iterate through remaining elements, tracking max in acc
def findMaxLoop : List Int → Int → Int
  | [], acc => acc
  | x :: rest, acc => findMaxLoop rest (if x > acc then x else acc)

-- Models: max = s[0]; for elem in s[1:]: if elem > max: max = elem; return max
def findMax (s : List Int) (hs : s ≠ []) : Int :=
  findMaxLoop s.tail (s.head hs)

-- Loop invariant 1: result ≥ accumulator
theorem findMaxLoop_ge_acc (rest : List Int) (acc : Int) :
    acc ≤ findMaxLoop rest acc := by
  induction rest generalizing acc with
  | nil => simp [findMaxLoop]
  | cons x t ih =>
    unfold findMaxLoop
    split
    · have := ih x; omega
    · exact ih acc

-- Loop invariant 2: result ≥ every element in the remaining list
theorem findMaxLoop_ge_all (rest : List Int) (acc : Int) :
    ∀ y ∈ rest, y ≤ findMaxLoop rest acc := by
  induction rest generalizing acc with
  | nil => simp
  | cons x t ih =>
    intro y hy
    unfold findMaxLoop
    rcases List.mem_cons.mp hy with rfl | hy'
    · -- y = x: after rfl, x is eliminated and y survives
      split
      · exact findMaxLoop_ge_acc t y
      · have := findMaxLoop_ge_acc t acc; omega
    · -- y ∈ t: x still in scope
      split
      · exact ih x y hy'
      · exact ih acc y hy'

-- Loop invariant 3: result is either the accumulator or an element of the list
theorem findMaxLoop_mem_or_eq (rest : List Int) (acc : Int) :
    findMaxLoop rest acc = acc ∨ findMaxLoop rest acc ∈ rest := by
  induction rest generalizing acc with
  | nil => simp [findMaxLoop]
  | cons x t ih =>
    unfold findMaxLoop
    split
    · rcases ih x with h | h
      · right; rw [h]; exact List.mem_cons.mpr (Or.inl rfl)
      · right; exact List.mem_cons.mpr (Or.inr h)
    · rcases ih acc with h | h
      · left; exact h
      · right; exact List.mem_cons.mpr (Or.inr h)

-- The algorithm satisfies both postconditions
theorem findMax_satisfies (s : List Int) (hs : s ≠ []) :
    findMax s hs ∈ s ∧ ∀ x ∈ s, x ≤ findMax s hs := by
  cases s with
  | nil => contradiction
  | cons a t =>
    simp only [findMax, List.head_cons, List.tail_cons]
    constructor
    · -- membership: result ∈ a :: t
      rcases findMaxLoop_mem_or_eq t a with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons.mpr (Or.inr h)
    · -- maximality: result ≥ everything
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · -- x = a: after rfl, a is eliminated, x survives
        exact findMaxLoop_ge_acc t x
      · exact findMaxLoop_ge_all t _ x hx'

-- Final: the algorithm witnesses the existential spec
theorem solution (s : List Int) (hs : s ≠ []) :
    ∃ max ∈ s, ∀ x ∈ s, x ≤ max :=
  ⟨findMax s hs, (findMax_satisfies s hs).1, (findMax_satisfies s hs).2⟩
