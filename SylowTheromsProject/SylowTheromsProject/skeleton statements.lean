import Mathlib.Tactic


--9
theorem card_union_disj_rangedef (n : ℕ) (V : (range n) → Set U)
 (hdisj : ∀ (i j : (range n)), Disjoint (V i) (V j))
 (hf : ∀ (i : (range n)), (V i).Finite) :
Nat.card (⋃ i, V i) = ∑ᶠ (i : (range n)), Nat.card (V i) := by
sorry
