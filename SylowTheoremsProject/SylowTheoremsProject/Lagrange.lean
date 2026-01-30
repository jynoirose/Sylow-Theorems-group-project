import SylowTheoremsProject.Imports
--This needs to be commented better, I will do it at somepoint
noncomputable section

variable {G : Type _} [Group G]

/-- The left-coset equivalence relation `a ~ b` iff `a⁻¹ * b ∈ H`. -/
def leftCosetRel (H : Subgroup G) : Setoid G :=
{ r := fun a b => a⁻¹ * b ∈ H,
  iseqv :=
  ⟨
    -- reflexivity
    by
      intro a
      have : a⁻¹ * a = (1 : G) := by simp
      simp [this, H.one_mem],
    -- symmetry
    by
      intro a b hab
      have : (a⁻¹ * b)⁻¹ = b⁻¹ * a := by simp [mul_inv_rev]
      have hmem : (a⁻¹ * b)⁻¹ ∈ H := H.inv_mem hab
      simpa [this] using hmem,
    -- transitivity
    by
      intro a b c hab hbc
      have : a⁻¹ * c = (a⁻¹ * b) * (b⁻¹ * c) := by simp [mul_assoc]
      simpa [this] using H.mul_mem hab hbc
  ⟩ }

namespace Subgroup

open Fintype

variable (H : Subgroup G) [Fintype G] [Fintype H]

local infix:70 " ⧸ " => fun G H => Quotient (leftCosetRel H)

/-- The quotient `G ⧸ H` is finite because `G` is finite. -/
noncomputable instance : Finite (G ⧸ H) :=
  Quotient.finite _

noncomputable instance : Fintype (G ⧸ H) :=
  Fintype.ofFinite _

/-- Choose a representative for each coset using `Classical.choose`. -/
noncomputable def rep (q : G ⧸ H) : G := Classical.choose (Quotient.exists_rep q)


lemma rep_spec (q : G ⧸ H) : Quotient.mk (s := leftCosetRel H) (rep (H := H) q) = q :=
  Classical.choose_spec (Quotient.exists_rep q)

/-- The bijection `G ≃ (G ⧸ H) × H` built from chosen representatives. -/
noncomputable def equiv_quotient_times_H : G ≃ (G ⧸ H) × H where
  toFun := fun g =>
    let q := Quotient.mk (s := leftCosetRel H) g
    let h : G := (rep (H := H) q)⁻¹ * g
    have h_mem : h ∈ H := by
      -- rep H q and g represent the same coset, so (rep H q)⁻¹ * g ∈ H
      have h_eq : Quotient.mk (s := leftCosetRel H) (rep (H := H) q) =
          Quotient.mk (s := leftCosetRel H) g := by
        simpa [q] using rep_spec (H := H) q
      have h_rel : (leftCosetRel H).r (rep (H := H) q) g := Quotient.exact h_eq
      simpa [leftCosetRel] using h_rel
    (q, ⟨h, h_mem⟩)
  invFun := fun p =>
    let q := p.1
    let h := p.2
    (rep (H := H) q) * (h : G)
  left_inv := by
    intro g
    change
      (rep (H := H) (Quotient.mk (s := leftCosetRel H) g)) *
        ((rep (H := H) (Quotient.mk (s := leftCosetRel H) g))⁻¹ * g) = g
    simp
  right_inv := by
    intro ⟨q, h⟩
    dsimp only [Equiv.toFun, Equiv.invFun]
    -- the quotient of rep q * h is the same coset q
    have q_eq :
        Quotient.mk (s := leftCosetRel H) ((rep (H := H) q) * (h : G)) = q := by
      calc
        Quotient.mk (s := leftCosetRel H) ((rep (H := H) q) * (h : G))
            = Quotient.mk (s := leftCosetRel H) (rep (H := H) q) := by
              refine Quotient.sound ?_
              -- unfold the relation: `(rep q * h)⁻¹ * rep q ∈ H`
              change ((rep (H := H) q) * (h : G))⁻¹ * rep (H := H) q ∈ H
              have h_eq :
                  ((rep (H := H) q) * (h : G))⁻¹ * rep (H := H) q = (h : G)⁻¹ := by
                simp
              -- `(h : G)⁻¹ ∈ H` because `h ∈ H`
              have hmem : (h : G)⁻¹ ∈ H := H.inv_mem h.property
              simpa [h_eq] using hmem
        _ = q := by simpa using rep_spec (H := H) q
    have h_simp :
        (rep (H := H) q)⁻¹ * (rep (H := H) q * (h : G)) = (h : G) := by
      simp
    simp [q_eq, h_simp]

/-- Counting identity `|G| = |G ⧸ H| * |H|` obtained from the explicit bijection. -/
theorem index_mul_card :
    Fintype.card G = Fintype.card (G⧸H) * Fintype.card H :=
by
  let e := equiv_quotient_times_H H
  -- `Fintype.card_congr e` has type `card ((G⧸H) × H) = card G`,
  have : Fintype.card G = Fintype.card ((G⧸H) × H) := Fintype.card_congr e
  calc
    Fintype.card G = Fintype.card ((G⧸H) × H) := this
    _ = Fintype.card (G⧸H) * Fintype.card H := by simp [Fintype.card_prod]

/-- **Lagrange's Theorem**: `|H| ∣ |G|`. -/
theorem Lagrange : Fintype.card (H : Type _) ∣ Fintype.card G := by
  use Fintype.card (G ⧸ H)
  -- expand `card G` using `index_mul_card` and then swap the product factors
  rw [index_mul_card (H := H), mul_comm]

end Subgroup





/-- Left coset `gH` as a `Set G`. -/
def leftCoset (H : Subgroup G) (g : G) : Set G := { x | g⁻¹ * x ∈ H }

lemma leftCoset_eq_of_mem {H : Subgroup G} {g k : G}
  (hk : k ∈ leftCoset H g) :
  leftCoset H g = leftCoset H k := by
  ext x
  constructor
  · intro hx
    have hxH : g⁻¹ * x ∈ H := hx
    have h_inv : (g⁻¹ * k)⁻¹ ∈ H := H.inv_mem hk
    have hx' : (g⁻¹ * k)⁻¹ * (g⁻¹ * x) ∈ H := H.mul_mem h_inv hxH
    simpa [leftCoset, mul_assoc] using hx'
  · intro hx
    have hxH : k⁻¹ * x ∈ H := hx
    have hx' : (g⁻¹ * k) * (k⁻¹ * x) ∈ H := H.mul_mem hk hxH
    simpa [leftCoset, mul_assoc] using hx'

--Lemma 1.15
theorem Eq_of_cosets {H : Subgroup G} {g k : G} :
  k ∈ leftCoset H g ↔ leftCoset H g = leftCoset H k := by
  constructor
  · intro hk
    exact leftCoset_eq_of_mem hk
  · intro hEq
    -- k ∈ leftCoset H k because 1 ∈ H
    have hk : k ∈ leftCoset H k := by
      change k⁻¹ * k ∈ H
      simp
    simpa [hEq] using hk


end
