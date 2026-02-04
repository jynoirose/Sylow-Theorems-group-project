import SylowTheoremsProject.Subprojects.Imports
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
      -- H is a subgroup therefore it is closed under inverses
      have hmem : (a⁻¹ * b)⁻¹ ∈ H := H.inv_mem hab
      simpa [this] using hmem,

    -- transitivity
    by
      intro a b c hab hbc
      have : a⁻¹ * c = (a⁻¹ * b) * (b⁻¹ * c) := by simp [mul_assoc]
      -- H is closed under multiplication
      simpa [this] using H.mul_mem hab hbc
  ⟩ }

namespace Subgroup

open Fintype

variable (H : Subgroup G) [Fintype G] [Fintype H]

/-- Notation for the quotient of `G` by the left-coset relation induced by `H`. -/
local infix:70 " ⧸ " => fun G H => Quotient (leftCosetRel H)

/-- The quotient `G ⧸ H` is finite because `G` is finite. -/
noncomputable instance : Finite (G ⧸ H) :=
  Quotient.finite _

/-- We need this to be a Fintype -/
noncomputable instance : Fintype (G ⧸ H) :=
  Fintype.ofFinite _

/--This becomes noncomputable as  for each coset in G ⧸ H, we choose a representative element of g-/
noncomputable def rep (q : G ⧸ H) : G := Classical.choose (Quotient.exists_rep q)

/--Checks that our chosen representative is in the correct coset-/
lemma rep_spec (q : G ⧸ H) : Quotient.mk (s := leftCosetRel H) (rep (H := H) q) = q :=
  Classical.choose_spec (Quotient.exists_rep q)

/-- The bijection `G ≃ (G ⧸ H) × H` built from chosen representatives.
We want to show that:
    For a given `g : G`,
    - Let `q` be its coset
    - Write `g = rep(q) * h` where `h ∈ H`
    - Then the map `g ↦ (q, h)` is a bijection between `G` and `(G ⧸ H) × H`.
-/
noncomputable def equiv_quotient_times_H : G ≃ (G ⧸ H) × H where
  -- Forward map - `(g) ↦ (q, h)`
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

  -- Inverse map - `(q, h) ↦ rep(q) * h`
  invFun := fun p =>
    let q := p.1
    let h := p.2
    (rep (H := H) q) * (h : G)

  left_inv := by
    intro g
    --The change allows us to turn this a group identity
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
      -- show mk(rep(q)*h) = mk(rep(q))
        Quotient.mk (s := leftCosetRel H) ((rep (H := H) q) * (h : G))
            = Quotient.mk (s := leftCosetRel H) (rep (H := H) q) := by
              refine Quotient.sound ?_
              -- Quotient.sound requires us to show that `(rep q * h)⁻¹ * rep q ∈ H`

              change ((rep (H := H) q) * (h : G))⁻¹ * rep (H := H) q ∈ H
              have h_eq :
                  ((rep (H := H) q) * (h : G))⁻¹ * rep (H := H) q = (h : G)⁻¹ := by
                simp

              -- `(h : G)⁻¹ ∈ H` because `h ∈ H`
              have hmem : (h : G)⁻¹ ∈ H := H.inv_mem h.property
              simpa [h_eq] using hmem
          -- now mk(rep(q)) = q by rep_spec
        _ = q := by simpa using rep_spec (H := H) q

    -- Now we can simplify the H expression `(rep(q))⁻¹ * (rep(q) * h) = h`
    have h_simp :
        (rep (H := H) q)⁻¹ * (rep (H := H) q * (h : G)) = (h : G) := by
      simp
      --We end up with the `(q, h)` as we wanted
    simp [q_eq, h_simp]

/-- Counting identity `|G| = |G ⧸ H| * |H|` obtained from the explicit bijection. -/
theorem index_mul_card :
    Fintype.card G = Fintype.card (G⧸H) * Fintype.card H :=
by
  let e := equiv_quotient_times_H H
   -- `Fintype.card_congr e` converts a bijection into an equality of cardinalities:
  calc
    Fintype.card G = Fintype.card ((G⧸H) × H) := Fintype.card_congr e
    _ = Fintype.card (G⧸H) * Fintype.card H := by simp [Fintype.card_prod]


/-- **Lagrange's Theorem**: `|H| ∣ |G|`. -/
theorem Lagrange : Fintype.card (H : Type _) ∣ Fintype.card G := by
  use Fintype.card (G ⧸ H)
  -- expand `card G` using `index_mul_card` and then swap the product factors
  rw [index_mul_card (H := H), mul_comm]

end Subgroup

end
