import Mathlib.Tactic

universe u v

def inj (X Y : Type u) (f : X → Y) := ∀ (x : X) , ∀ (y : X) , f x = f y → x = y
def surj (X Y : Type u) (f : X → Y) := ∀ (y : Y) , ∃ (x : X) , f x = y
def bij (X Y : Type u) (f : X → Y) := inj X Y f ∧ surj X Y f
def image_of_func (X Y : Type u) (f : X → Y) : Set Y := {y : Y | ∃ x : X, f x = y}


/-
#print image_of_func
--a bijection is an injection
lemma bij_is_inj {G : Type u} {H : Type u} [Finite G] [Finite H]
 (f : G → H) : bij G H f →  inj G H f := by
intro h
cases h with
| intro left right
exact left
done
--a bijection is a surjection
lemma bij_is_surj {G : Type u} {H : Type u} [Finite G] [Finite H]
 (f : G → H) : bij G H f →  surj G H f := by
intro h
cases h with
| intro left right
exact right
done
-/
lemma inj_card {G : Type u} {H : Type u} [Finite G] [Finite H]
(a b : ℕ) (hg : Nat.card G = a) (hh : Nat.card H = b) (f : G → H) (hinj : inj G H f) : a ≤ b := by
rw[← hh, ← hg]
exact Nat.card_le_card_of_injective f hinj
--image has cardinality same as G
--if subset has cardinality α then set has cardinality ≥ α
done

--the image of a surjection has the same order as the set the surjection maps to (for both finite)
lemma surj_card {G : Type u} {H : Type u} [Finite G] [Finite H]
(a b : ℕ) (hg : Nat.card G = a) (hh : Nat.card H = b) (f : G → H) (hsurj : surj G H f) : b ≤ a := by
rw[← hh, ← hg]
exact Nat.card_le_card_of_surjective f hsurj
done


--if there's a bijection between two finite sets then the sets have the same order
theorem bij_card {G : Type u} {H : Type u} [Finite G] [Finite H]
(a b : ℕ) (hg : Nat.card G = a) (hh : Nat.card H = b) (f : G → H) (hbij : bij G H f) : a = b := by
apply le_antisymm
cases hbij with
| intro left right
· exact inj_card a b hg hh f left
cases hbij with
| intro left right
· exact surj_card a b hg hh f right
done
