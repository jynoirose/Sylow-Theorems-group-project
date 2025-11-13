import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Index
import Mathlib.Data.Fintype.OfMap
import Mathlib.GroupTheory.Coset.Defs

open MulAction

--state those variables
-- variable {G X : Type*} [Group G] [MulAction G X] [Fintype G] [Fintype X] [DecidableEq X]
-- variable (x : X)

-- #check MulAction.orbit G x
-- #check MulAction.stabilizer G x


-- example (x : X) : Set X :=
--   MulAction.orbit G x


--Since Lean does not know Orb_G(x) is a finite set, Or because it's me not find the lemma.
--We need to tell Lean Orb_G(x) is a finite set, then we can use its Fintype.card in the theorem.
lemma orbit_finite {G X : Type*} [Group G] [MulAction G X] [Fintype G] (x : X) :
    (orbit G x).Finite := by
  have : orbit G x = Set.range (fun g : G => g • x) := by
    ext y
    simp [mem_orbit_iff]
  rw [this]
  exact Set.finite_range _

noncomputable instance orbit_fintype {G X : Type*} [Group G] [MulAction G X]
    [Fintype G] (x : X) : Fintype (orbit G x) :=
  (orbit_finite x).fintype



-- open QuotientGroup
-- We need to prove that f : G/Stab_G(x) → Orb_G(x) is a bijective.
-- First we set Y = G/Stab_G(x), then it becomes f : Y → Orb_G(x).
-- #check QuotientGroup.leftRel
-- #check MulAction.stabilizer G x

-- def orbit (x : X) : Set X := {y | ∃ g : G, g • x = y}


-- define the map that in the theorem.
def orbitMap {G : Type*} [Group G] {X : Type*} [MulAction G X] (x : X) :
  G ⧸ stabilizer G x → orbit G x :=
  Quotient.lift
    (fun g : G => ⟨g • x, ⟨g, rfl⟩⟩)
    (by
      intro a b h
      simp only [Subtype.mk_eq_mk]
      have : a⁻¹ * b ∈ stabilizer G x := QuotientGroup.leftRel_apply.mp h
      have hx : (a⁻¹ * b) • x = x := mem_stabilizer_iff.mp this
      calc
        a • x
          = a • ((a⁻¹ * b) • x) := by rw [hx]
        _ = (a * (a⁻¹ * b)) • x := by rw [← mul_smul]
        _ = ((a * a⁻¹) * b) • x := by rw [mul_assoc]
        _ = (1 * b) • x := by rw [mul_inv_cancel]
        _ = b • x := by rw [one_mul])

--prove this map is injective.
lemma orbitMap_injective_on {G : Type*} [Group G] {X : Type*} [MulAction G X] (x : X) :
  Set.InjOn (fun q : G ⧸ stabilizer G x => (orbitMap x q).val) Set.univ := by
  intro a _ b _ h
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>

  simp only [orbitMap, Quotient.lift_mk] at h

  have : (a⁻¹ * b) • x = x := by
    calc
      (a⁻¹ * b) • x
        = a⁻¹ • (b • x) := by rw [mul_smul]
      _ = a⁻¹ • (a • x) := by rw [← h]
      _ = (a⁻¹ * a) • x := by rw [← mul_smul]
      _ = (1 : G) • x := by rw [inv_mul_cancel]
      _ = x := by rw [one_smul]

  have mem_stab : a⁻¹ * b ∈ stabilizer G x :=
    mem_stabilizer_iff.mpr this

  apply Quotient.sound
  exact QuotientGroup.leftRel_apply.mpr mem_stab


--prove it is surjective.
lemma orbitMap_surjective_on {G : Type*} [Group G] {X : Type*} [MulAction G X] (x : X) :
  Set.SurjOn (fun q : G ⧸ stabilizer G x => (orbitMap x q).val)
    Set.univ (orbit G x) := by
  intro y hy
  obtain ⟨g, rfl⟩  := hy
  use Quotient.mk _ g
  constructor
  · trivial
  · simp only [orbitMap, Quotient.lift_mk]



--prove it is bijective.
lemma orbitMap_bijective {G : Type*} [Group G] {X : Type*} [MulAction G X] (x : X) :
  Function.Bijective (orbitMap (G := G) (X := X) x) := by
  constructor
  · -- inj
    intro a b h
    have : (orbitMap x a).val = (orbitMap x b).val := by
      rw [h]
    exact orbitMap_injective_on x (Set.mem_univ a) (Set.mem_univ b) this
  · -- sub
    intro y
    have hy : y.val ∈ orbit G x := y.property
    obtain ⟨q, _, hq⟩ := orbitMap_surjective_on x hy
    use q
    exact Subtype.ext hq


theorem orbit_stabilizer_theorem
  (G : Type*) [Group G] [Fintype G]
  (X : Type*) [MulAction G X] [DecidableEq X]
  (x : X) :
  Fintype.card G = Fintype.card (orbit G x) * Fintype.card (stabilizer G x) := by

  let : Fintype (orbit G x) := orbit_fintype x

  calc Fintype.card G
      = Nat.card G := Nat.card_eq_fintype_card.symm
    _ = Nat.card (G ⧸ stabilizer G x) * Nat.card (stabilizer G x) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup (stabilizer G x)
    _ = Fintype.card (G ⧸ stabilizer G x) * Fintype.card (stabilizer G x) := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    _ = Fintype.card (orbit G x) * Fintype.card (stabilizer G x) := by
        rw [Fintype.card_of_bijective (orbitMap_bijective (G := G) (X := X) x)]


-- Cor of the orbit Stabilizer theorem
--One
