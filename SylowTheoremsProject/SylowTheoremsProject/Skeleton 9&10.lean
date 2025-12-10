--skeleton 9 & 10
import Mathlib.Tactic
import Mathlib.Data.Set.Card.Arithmetic

--open Set
open Fintype
open Finset
universe u v

variable {α : Type*} (I : Finset α) (p : ℕ) (Prime p)
--says p divides the order of each set in the sum indezed over range n

def icard {U : Type u} {I : Type v} [Fintype I]
{V : I → Set U} (i : I) (hV : ∀ (i : I), Fintype (V i))
: ℕ := Fintype.card (V i)

/- check definition of icard makes sense
example {U : Type u} {I : Type v} [Fintype I]
(V : I → Set U) (hV : ∀ (i : I), Fintype (V i)) (i : I)
 : icard i hV = Fintype.card (V i) := by
  unfold icard
  trivial
-/

--skeleton (9)
theorem card_union_disj {U : Type u} {I : Type v} [Fintype I]
{V : I → Set U} (hV : ∀ (i : I), (V i).Finite)
(hdisj : ∀ (k j : I), Disjoint (V k) (V j)) :
(⋃ (i : I), V i).ncard = ∑ᶠ (i : I), (V i).ncard := by
  have h₀ : Pairwise (Function.onFun Disjoint V) := by
    exact fun ⦃i j⦄ a ↦ hdisj i j
  apply Set.ncard_iUnion_of_finite hV h₀

--skeleton (10)
-- says if p ∤ Σ|Vᵢ| then p ∤ |Vᵢ| for some i
lemma not_div_sum {U : Type u} {I : Type v} [Fintype I]
{V : I → Set U} (hV : ∀ (i : I), Fintype (V i)) :
 ¬ (p ∣ ∑ᶠ (i : I), Fintype.card (V i))
 → ∃ (i : I), ¬ (p ∣ Fintype.card (V i)) := by
contrapose
simp
intro hx
·
  have h₃ : ∑ᶠ (i : I), Fintype.card (V i) = ∑ᶠ (i : I), icard i hV := by
    unfold icard
    trivial
  have h₄ : ∀ (i : I), p ∣ icard i hV := by
    unfold icard
    apply hx
  rw[h₃]
  rw[finsum_eq_sum_of_fintype]
  apply dvd_sum
  exact fun i a ↦ hx i

--define the set of all i in I such that p ∤ |Vᵢ|
def notdivset {U : Type u} {I : Type v} [Fintype I] (p : ℕ)
{V : I → Set U} (hV : ∀ (i : I), Fintype (V i))
 := {k : I | ¬ (p ∣ Fintype.card (V k))}

--gives the subset J of the index I of the sum so that we can split the sum
-- into a sum over J, where p ∤ |Vⱼ| and a sum over I \ J where p | |Vᵢ|
lemma notdiv_index_subset {U : Type u} {I : Type v} [Fintype I] (p : ℕ)
{V : I → Set U} (hV : ∀ (i : I), Fintype (V i))
(hdiv : ¬ (p ∣ ∑ᶠ (i : I), Fintype.card (V i))) :
 ∃ (J : Finset I), Nonempty J → ∀ (j : J), ¬ (p ∣ Fintype.card (V j)) := by
  have h₀ : ∃ (k : I), ¬ (p ∣ Fintype.card (V k)) := by
    apply not_div_sum
    exact hdiv
  have h₁ : Nonempty (notdivset p hV) := by
    unfold notdivset
    exact nonempty_subtype.mpr h₀
  have h₂ : Fintype (notdivset p hV) := by
    exact ofFinite ↑(notdivset p hV)
  use (notdivset p hV).toFinset
  simp
  exact fun x h a b ↦ b

/-unsure if we need
lemma rearrange_10 {U : Type u} {I : Type v} [Fintype I] (p : ℕ)
{V : I → Set U} (hV : ∀ (i : I), Fintype (V i))
(hdiv : ¬ (p ∣ ∑ᶠ (i : I), Fintype.card (V i))) :
 ∃ (J : Finset I), Nonempty J → ∀ (j : J), ¬ (p ∣ Fintype.card (V j))
  → ∀ (i : I), i ∉ J → (p ∣ Fintype.card (V i)) := by
  have h₀ : ∃ (J : Finset I), Nonempty J → ∀ (j : J), ¬ (p ∣ Fintype.card (V j)) := by
   exact notdiv_index_subset p hV hdiv
  sorry
  --have h₁ : {i : I | p ∣ Fintype.card (V i)} = {i : I | i ∉ J}
  --lean can;t work out what J is

-/
