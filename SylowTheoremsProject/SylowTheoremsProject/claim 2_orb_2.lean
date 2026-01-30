import Mathlib.Tactic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Nat.Prime.Basic

import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Index
import Mathlib.Data.Fintype.OfMap
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Sylow

import Mathlib.Data.Set.Restrict
--open Set
open Fintype
open Finset
universe u v

open MulAction


-- The following lemma states that orbits are finite
-- G is a finite group that can act on X, x is an element in X
-- The conclusion to prove is that the set Orb_G(X) is finite
lemma orbit_finite {G X : Type*} [Group G] [MulAction G X] [Fintype G] (x : X) :
  (orbit G x).Finite := by

  -- We first prove that Orb_G(x) is the same thing as the image of the function g • x
  have : orbit G x = Set.range (fun g : G => g • x) := by
    ext y
    -- Change the goal to:
    -- assuming y belongs to Orbit_G(x), it's equivalent to y also satisfying the right-hand side
    simp [mem_orbit_iff] -- Simplify the goal to: there exists some g such that g • x = y
  rw [this] -- Rewrite using what we just derived
  -- the goal becomes proving Set.range (fun g : G => g • x) is finite
  exact Set.finite_range _ -- Since G is finite, the range of the function is also finite



-- We've already shown the finiteness of Orb_G(X)
-- now wrap it as a noncomputable instance for convenient use in Lean
noncomputable instance orbit_fintype {G X : Type*} [Group G] [MulAction G X]
    [Fintype G] (x : X) : Fintype (orbit G x) :=
  (orbit_finite x).fintype


-- Define orbitMap: G/Stab(x) → Orbit(x), we need to prove this definition is well-defined
def orbitMap {G : Type*} [Group G] {X : Type*} [MulAction G X] (x : X) :
  G ⧸ stabilizer G x → orbit G x :=
  Quotient.lift -- Need to provide a representative and proof
    (fun g : G => ⟨g • x, ⟨g, rfl⟩⟩) -- Give a point g • x, and proof ∃ g', g' • x = g • x
    (by -- Start proving a • x = b • x
      intro a b h
      -- Introduce a and b, h is a ≈ b, assuming they are equivalent in the quotient group
      simp only [Subtype.mk_eq_mk] -- Rewrite the goal as the corresponding a • x = b • x

      -- Show that a⁻¹ * b is in the stabilizer
      have : a⁻¹ * b ∈ stabilizer G x := by
        apply QuotientGroup.leftRel_apply.mp
        -- 'a and b are equivalent in the quotient group' <=> 'a⁻¹ * b is in the stabilizer‘
        -- use the left-to-right direction of this property
        exact h

      -- Continue to show that (a⁻¹ * b) • x = x
      have hx : (a⁻¹ * b) • x = x := mem_stabilizer_iff.mp this

      -- Calculate well-definedness, i.e., prove a • x = b • x
      calc
        a • x
          = a • ((a⁻¹ * b) • x) := by rw [hx]
        _ = (a * (a⁻¹ * b)) • x := by rw [← mul_smul]
        _ = ((a * a⁻¹) * b) • x := by rw [mul_assoc]
        _ = (1 * b) • x := by rw [mul_inv_cancel]
        _ = b • x := by rw [one_mul])



-- Below we prove that orbitMap: G/Stab_G(x) → Orbit_G(x) is injective
lemma orbitMap_injective_on {G : Type*} [Group G] {X : Type*} [MulAction G X] (x : X) :
  Set.InjOn (fun q : G ⧸ stabilizer G x => (orbitMap x q).val) Set.univ := by
  -- The goal is to prove:
  -- the function orbitMap is injective on the entire set univ (the whole domain)

  intro a _ b _ h
  -- Introduce a and b as elements in G/Stab(x)
  -- _ are univ, h is (orbitMap x a).val = (orbitMap x b).val

  -- Use induction on the quotient, replace a with a concrete representative element a,
  -- so a is an element of G, and do the same for b
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>

  simp only [orbitMap, Quotient.lift_mk] at h -- Simplify h to a • x = b • x

  -- Now prove (a⁻¹ * b) • x = x
  have : (a⁻¹ * b) • x = x := by
    calc
      (a⁻¹ * b) • x
        = a⁻¹ • (b • x) := by rw [mul_smul]
      _ = a⁻¹ • (a • x) := by rw [← h]
      _ = (a⁻¹ * a) • x := by rw [← mul_smul]
      _ = (1 : G) • x := by rw [inv_mul_cancel]
      _ = x := by rw [one_smul]

  -- Show that a⁻¹ * b is an element in the stabilizer
  have mem_stab : a⁻¹ * b ∈ stabilizer G x := by
    apply mem_stabilizer_iff.mpr -- Use the right-to-left direction of the lemma
    exact this

  apply Quotient.sound
  -- Simplify the goal from equivalence class equality ⟦a⟧ = ⟦b⟧ to just need to prove a ≈ b
  apply QuotientGroup.leftRel_apply.mpr
  -- Use the right-to-left direction of (a ≈ b) ↔ a⁻¹ * b ∈ stabilizer G x,
  -- so the new goal is a⁻¹ * b ∈ stabilizer G x
  exact mem_stab


-- Prove that orbitMap: G/Stab_G(x) → Orbit_G(x) is surjective
lemma orbitMap_surjective_on {G : Type*} [Group G] {X : Type*} [MulAction G X] (x : X) :
  Set.SurjOn (fun q : G ⧸ stabilizer G x => (orbitMap x q).val)
    Set.univ (orbit G x) := by

  -- In other words, if f(q) = (orbitMap x q).val,
  -- we need to prove ∀ y ∈ orbit G x, ∃ q, q ∈ univ ∧ f q = y
  intro y hy -- Introduce y as an element in X, hy is y ∈ orbit G x
  obtain ⟨g, rfl⟩ := hy
  -- Destructure hy to get ∃ g : G, y = g • x, then use rfl to replace all y with g • x
  use Quotient.mk _ g -- Take the representative element g in the quotient, i.e., ⟦g⟧
  constructor -- Since the goal is to prove ∃ q, q ∈ univ ∧ f q = g • x, split into two parts
  · trivial
  · simp only [orbitMap, Quotient.lift_mk] -- From ⟦g⟧ it becomes g • x



-- Prove that orbitMap: G/Stab_G(x) → Orbit_G(x) is bijective,
-- and lift from the value level to the function level
lemma orbitMap_bijective {G : Type*} [Group G] {X : Type*} [MulAction G X] (x : X) :
  Function.Bijective (orbitMap (G := G) (X := X) x) := by
  constructor -- Split into two parts: injectivity and surjectivity
  · -- Injectivity, goal is orbitMap x a = orbitMap x b → a = b
    intro a b h -- a and b are elements in G/Stab_G(x), h is orbitMap x a = orbitMap x b
    -- Show that extracting the elements from both sides of h gives equality
    have : (orbitMap x a).val = (orbitMap x b).val := by
      rw [h]

    -- Apply the injectivity lemma we proved earlier, which needs four values: a, b; a and b ∈ univ;
    --  and finally (orbitMap x a).val = (orbitMap x b).val
    exact orbitMap_injective_on x (Set.mem_univ a) (Set.mem_univ b) this
  · -- Surjectivity, goal is ∀ y, ∃ x, f x = y
    intro y -- Introduce y : orbit G x

    -- Extract y.val ∈ orbit G x for convenient use
    have hy : y.val ∈ orbit G x := y.property

    -- From the surjectivity we proved earlier, destructure to get q : G ⧸ stabilizer G x,
    --  _ is q ∈ univ (not used so omitted), hq : (orbitMap x q).val = y.val
    obtain ⟨q, _, hq⟩ := orbitMap_surjective_on x hy
    use q
    exact Subtype.ext hq -- Use Subtype.ext to automatically get orbitMap x q = y

-- Proof of the orbit-stabilizer theorem
theorem orbit_stabilizer_theorem
  (G : Type*) [Group G] [Fintype G]
  (X : Type*) [MulAction G X] [DecidableEq X]
  (x : X) :
  Fintype.card G = Fintype.card (orbit G x) * Fintype.card (stabilizer G x) := by

  calc Fintype.card G
      -- We want to change Fintype.card G to Nat.card G
      = Nat.card G := Nat.card_eq_fintype_card.symm

      -- Write |G| as |G/Stab| * |Stab|
    _ = Nat.card (G ⧸ stabilizer G x) * Nat.card (stabilizer G x) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup (stabilizer G x)

      -- Change Nat.card G back to Fintype.card G
    _ = Fintype.card (G ⧸ stabilizer G x) * Fintype.card (stabilizer G x) := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

      -- Use the bijection proved earlier to change
      -- Fintype.card (G ⧸ stabilizer G x) to Fintype.card (orbit G x)
    _ = Fintype.card (orbit G x) * Fintype.card (stabilizer G x) := by
        rw [Fintype.card_of_bijective (orbitMap_bijective (G := G) (X := X) x)]


-- Below we prove some related properties and corollaries of the orbit-stabilizer theorem


-- Corollary 2.17 (i): Any two orbits are either completely the same or completely disjoint
theorem orbit_disjoint_or_eq {G X : Type*} [Group G] [MulAction G X] (x y : X) :
    orbit G x = orbit G y ∨ Disjoint (orbit G x) (orbit G y) := by
  by_cases h : ∃ g : G, g • x = y
  · -- If there exists g such that g • x = y, then prove the two orbits are equal
    left -- Change the goal to the left part: orbit G x = orbit G y
    obtain ⟨g, hg⟩ := h -- Destructure h to get the concrete g and hg: g • x = y
    ext z -- Change the goal to z ∈ orbit G x ↔ z ∈ orbit G y
    constructor -- Split into left-to-right and right-to-left
    · -- First part: given z ∈ orbit G x, prove z ∈ orbit G y
      intro ⟨g1, hg1⟩ -- Introduce g1 satisfying z = g1 • x

      -- Calculate (g1 * g⁻¹) • y = z,
      -- which shows that there exists (g1 * g⁻¹) as an element in G such that z ∈ orbit G y
      use g1 * g⁻¹
      calc (g1 * g⁻¹) • y
          = g1 • (g⁻¹ • y) := by rw [mul_smul]
        _ = g1 • (g⁻¹ • (g • x)) := by rw [← hg]
        _ = g1 • ((g⁻¹ * g) • x) := by rw [mul_smul]
        _ = g1 • ((1 : G) • x) := by rw [inv_mul_cancel]
        _ = g1 • x := by rw [one_smul]
        _ = z := hg1

    · -- Second part: given z ∈ orbit G y, prove z ∈ orbit G x
      intro ⟨g2, hg2⟩ -- Introduce g2 satisfying z = g2 • y

      -- Find g2 * g as an element in G satisfying (g2 * g) • x = z, which proves z ∈ orbit G x
      use g2 * g
      calc (g2 * g) • x
          = g2 • (g • x) := by rw [mul_smul]
        _ = g2 • y := by rw [hg]
        _ = z := hg2
  · -- If no such g exists, then prove the two orbits are disjoint
    right -- The goal is the right part: Disjoint (orbit G x) (orbit G y)
    rw [Set.disjoint_iff]
    intro z ⟨⟨g1, hg1⟩, ⟨g2, hg2⟩⟩
    -- Introduce z, g1 and g2 satisfying g1 • x = z and g2 • y = z,
    -- assume z is in both orbits, need to find a contradiction
    apply h -- h is that there does not exist g : G, g • x = y
    -- Construct such a g to contradict h
    use g2⁻¹ * g1
    calc (g2⁻¹ * g1) • x
        = g2⁻¹ • (g1 • x) := by rw [mul_smul]
      _ = g2⁻¹ • z := by rw [← hg1]
      _ = g2⁻¹ • (g2 • y) := by rw [← hg2]
      _ = (g2⁻¹ * g2) • y := by rw [← mul_smul]
      _ = y := by rw [inv_mul_cancel, one_smul]

-- Corollary 2.17 (ii): Orbits form a partition of X
theorem orbits_partition {G X : Type*} [Group G] [MulAction G X] :
    (Set.range (orbit G : X → Set X)).PairwiseDisjoint id := by
  intro A hA B hB hAB -- Introduce sets A and B as elements in the orbits, with A ≠ B
  rcases hA with ⟨x, rfl⟩ -- Write set A as A = orbit G x
  rcases hB with ⟨y, rfl⟩ -- Write set B as B = orbit G y
  -- Apply the previously proved theorem: orbits are either equal or disjoint
  have h := orbit_disjoint_or_eq (G := G) (X := X) x y
  rcases h with h_eq | h_disj
  · -- If the orbits are equal, this contradicts A ≠ B
    contradiction
  · -- So they must be disjoint
    exact h_disj


-- Corollary 2.17 (iii): |Orb(x)| divides |G|
theorem orbit_card_dvd_group_card
    {G X : Type*} [Group G] [Fintype G] [MulAction G X] [DecidableEq X] (x : X) :
    Fintype.card (orbit G x) ∣ Fintype.card G := by
  have h := orbit_stabilizer_theorem G X x -- Apply the orbit-stabilizer theorem
  rw [h]
  simp [dvd_mul_right] -- Use a ∣ a * b to directly obtain the result

----
-- Finset.powersetCard in mathlib
-- define X(G,p,n) = {S ⊆ G | |S| = p ^ n}
def X (G : Type*) [Group G] (p n : ℕ) : Set (Set G) :=
  {S : Set G | Nat.card S = p ^ n}

-- G is a finite group
variable {G : Type*} [Group G] [Fintype G] (p n : ℕ)

-- define leftmulaction G(X G p n) which is g • S = gS = {g * s | s ∈ S}
instance instMulActionGX : MulAction G (X G p n) where

  -- Define the scalar multiplication: g • S is obtained by left-multiplying each element of S by g
  smul g S := ⟨(fun s => g * s) '' S.val, by
    -- Get the property of S (S satisfies the defining condition of X)
    have h := S.property
    simp only [X, Set.mem_setOf_eq] at h -- Simplify in hypothesis h
    simp only [X, Set.mem_setOf_eq] -- Simplify in goal
    rw [Nat.card_image_of_injective]
    -- Under an injective function
    -- the cardinality of the image equals the cardinality of the preimage
    · exact h -- Prove that |gS| = |S|
    · exact mul_right_injective g⟩ -- Prove that left multiplication by g is injective

  -- Prove the identity property: 1 • S = S
  one_smul S := by
    ext x
    constructor -- Prove both directions

    -- if x ∈ 1 • S, then x ∈ S
    · rintro ⟨y, hy, rfl⟩ -- x = 1 * y, where y ∈ S
      simpa using hy -- Simplify to get x = y ∈ S
    -- if x ∈ S, then x ∈ 1 • S
    · intro hx -- Assume x ∈ S
      exact ⟨x, hx, one_mul x⟩ -- x = 1 * x, where x ∈ S

  -- Prove associativity: (g1 * g2) • S = g1 • (g2 • S)
  mul_smul g1 g2 S := by
    ext x
    constructor

    -- if x ∈ g1 • (g2 • S), then x ∈ (g1 * g2) • S
    · intro hx
      obtain ⟨s, hs, rfl⟩ := hx
      -- x ∈ g1 • (g2 • S) means there exists s such that x = g1 * s and s ∈ g2 • S
      use g2 * s
      constructor
      · use s, hs -- Prove that g2 * s ∈ g2 • S
      · simp [mul_assoc] -- Prove x = g1 * (g2 * s) = (g1 * g2) * s

    -- if x ∈ (g1 * g2) • S, then x ∈ g1 • (g2 • S)
    · intro hx
      obtain ⟨t, ht, rfl⟩ := hx
      obtain ⟨s, hs, rfl⟩ := ht
      use s, hs
      simp [mul_assoc]


-- Claim one : Stab_G(S_i) = S_i
-- This theorem shows that if the underlying set of H_i is S_i,
-- then the stabilizer of S_i (as a set) also equals S_i
theorem claim_1_seteq {G : Type*} [Group G] {p n r : ℕ}
    (S : Fin r → X G p n)
    (H : Fin r → Subgroup G)
    -- Hypothesis: the underlying set of each subgroup H_i equals S_i
    (hH : ∀ i, (H i : Set G) = (S i).val)
    (i : Fin r) :
    (stabilizer G (S i) : Set G) = (S i).val := by
  ext g
  constructor

  -- if g is in the stabilizer of S_i, then g ∈ S_i
  · intro hg -- Assume g ∈ Stab_G(S_i), i.e., g • S_i = S_i
    have h1_in_Si : (1 : G) ∈ (S i).val := by -- First prove that 1 ∈ S_i
      rw [← hH i] -- Rewrite S_i as H_i
      exact OneMemClass.one_mem (H i) -- H_i is a subgroup, so it contains the identity

    -- Prove that the underlying set of S_i equals that of g • S_i
    have : (S i).val = (g • S i).val := by
      rw [hg] -- Use g • S_i = S_i
    rw [this] -- Show g ∈ g • S_i: since 1 ∈ S_i, we have g * 1 = g ∈ g • S_i
    exact ⟨1, h1_in_Si, mul_one g⟩

  -- if g ∈ S_i, then g is in the stabilizer of S_i
  · intro hg_in_Si -- Assume g ∈ S_i
    ext x
    constructor

    -- if x ∈ g • S_i, then x ∈ S_i
    · intro hx
      obtain ⟨s, hs, rfl⟩ := hx -- x ∈ g • S_i means there exists s ∈ S_i such that x = g * s
      rw [← hH i] at hg_in_Si hs -- Rewrite S_i as H_i in hypotheses
      rw [← hH i] -- -- Rewrite S_i as H_i in goal
      exact mul_mem hg_in_Si hs -- In a subgroup, g ∈ H_i and s ∈ H_i implies g * s ∈ H_i

    -- if x ∈ S_i, then x ∈ g • S_i
    · intro hx
      use g⁻¹ * x
      constructor
      -- Prove g⁻¹ * x ∈ S_i: view S_i as the subgroup H_i
      · rw [← hH i] at hg_in_Si hx ⊢
        exact mul_mem (inv_mem hg_in_Si) hx
      · exact mul_inv_cancel_left g x -- Prove x = g * (g⁻¹ * x)

-- Stab_G(S_i) = S_i is a subgroup
-- Corollary: the stabilizer Stab_G(S_i) equals H_i as subgroups,
-- meaning not only are the underlying sets equal, but the subgroup structures are also equal
theorem claim_1_subgroup {G : Type*} [Group G] {p n r : ℕ}
    (S : Fin r → X G p n)
    (H : Fin r → Subgroup G)
    (hH : ∀ i, (H i : Set G) = (S i).val)
    (i : Fin r) :
    H i = stabilizer G (S i) := by
  have h := claim_1_seteq S H hH i -- Use claim_1_seteq to obtain set-level equality
  -- Lift set equality to subgroup equality via injectivity of underlying sets
  apply SetLike.coe_injective
  rw [hH i, h]

-- prove card of H i is p^n
-- If the underlying set of subgroup H equals S.val, then the cardinality of H is p^n
lemma H_card_eq_pow {G : Type*} [Group G] [Fintype G] {p n : ℕ}
    (S : X G p n)
    (H : Subgroup G)
    (hH : (H : Set G) = S.val) :
    Nat.card H = p ^ n := by
  -- by prop of S, we have |S.val| = p^n
  have hS : Nat.card S.val = p ^ n := S.property
  -- because H set = S.val
  have : Nat.card (H : Set G) = Nat.card S.val := by
    rw [hH] -- ewrite H as S.val
  rw [hS] at this
  exact this


-- if |H| = p^n，then H is a p-group
lemma isPGroup_of_card_eq_prime_pow {G : Type*} [Group G] {p n : ℕ} [Fact p.Prime]
    (H : Subgroup G) [Fintype H] (h : Fintype.card H = p ^ n) : IsPGroup p H := by
  rw [IsPGroup.iff_card] -- Use the cardinality of p-groups
  exact ⟨n, by rw [Nat.card_eq_fintype_card]; exact h⟩

-- convert cardinality equality from Nat.card form to Fintype.card form
lemma fintype_card_of_nat_card {G : Type*} [Group G] [Fintype G] {p n : ℕ}
    (H : Subgroup G) [Fintype H]
    (h : Nat.card H = p ^ n) : -- Hypothesis: cardinality of H is p^n using Nat.card
    Fintype.card H = p ^ n := by -- Conclusion: cardinality of H is p^n using Fintype.card
  rw [← Nat.card_eq_fintype_card]
  exact h


-- main thorem of Claim one：H i (group version of S_i) is Sylow p-group
-- A Sylow p-subgroup:
-- (1) it is a p-group
-- (2) it is maximal among p-subgroups under inclusion
theorem H_is_sylow {G : Type*} [Group G] [Fintype G] {p n : ℕ}
    [hp : Fact p.Prime] -- p is prime
    (h_pn1_not_dvd : ¬ (p ^ (n + 1) ∣ Fintype.card G)) -- Hypothesis: p^(n+1) does not divide |G|
    (H : Subgroup G) -- H is a subgroup of G
    (hH_card : Nat.card H = p ^ n) : -- Hypothesis: the cardinality of H is p^n
    IsPGroup p H ∧ ∀ (K : Subgroup G), IsPGroup p K → H ≤ K → H = K := by

  haveI : Fintype H := Fintype.ofFinite H -- Ensure H has a Fintype instance
  have hH_fintype_card : Fintype.card H = p ^ n := by
    -- Convert cardinality from Nat.card form to Fintype.card form
    exact fintype_card_of_nat_card H hH_card
  constructor

  -- Part 1: prove H is a p-group
  · exact isPGroup_of_card_eq_prime_pow H hH_fintype_card

  -- Part 2: prove maximality of H, i.e., for any p-subgroup K, if H ≤ K, then H = K
  · intro K hK_pgroup hHK -- Assume K is a p-group and H ≤ K
    by_contra hne -- Proof by contradiction: assume H ≠ K
    have hH_lt_K : H < K := lt_of_le_of_ne hHK hne -- Then H < K

    haveI : Fintype K := Fintype.ofFinite K -- Ensure K has a Fintype instance

    have card_lt : Fintype.card H < Fintype.card K := -- Prove |H| < |K|
      Set.card_lt_card (SetLike.coe_ssubset_coe.mpr hH_lt_K)

    -- Since K is a p-group, there exists m such that |K| = p^m
    obtain ⟨m, hm⟩ := hK_pgroup.exists_card_eq
    rw [Nat.card_eq_fintype_card] at hm -- Convert Nat.card to Fintype.card

    -- The cardinality of K divides the cardinality of G (Lagrange's theorem)
    have hK_dvd : Fintype.card K ∣ Fintype.card G := by
      have := Subgroup.card_subgroup_dvd_card K
      simp only [Nat.card_eq_fintype_card] at this
      exact this

    rw [hH_fintype_card, hm] at card_lt -- From p^n < p^m, deduce n < m (since p > 1)
    have hn_lt_m : n < m := (Nat.pow_lt_pow_iff_right hp.out.one_lt).mp card_lt

    -- Derive a contradiction: prove p^(n+1) ∣ |G|
    have : p ^ (n + 1) ∣ Fintype.card G := by
      have h_n1_le_m : n + 1 ≤ m := hn_lt_m -- From n < m, deduce n + 1 ≤ m
      have h_pn1_dvd_pm : p ^ (n + 1) ∣ p ^ m := by -- Therefore p^(n+1) ∣ p^m
        exact Nat.pow_dvd_pow p h_n1_le_m
      -- Also p^m = |K| ∣ |G|, so by transitivity of divisibility, p^(n+1) ∣ |G|
      have h_pm_dvd_G : p ^ m ∣ Fintype.card G := by
        rw [← hm]
        exact hK_dvd
      exact Nat.dvd_trans h_pn1_dvd_pm h_pm_dvd_G

    exact h_pn1_not_dvd this -- This contradicts the hypothesis

variable {α : Type*} (I : Finset α) (p : ℕ)
--says p divides the order of each set in the sum indezed over range n

def icard {U : Type u} {I : Type v} [Fintype I]
{V : I → Set U} (i : I) (hV : ∀ (i : I), Fintype (V i))
: ℕ := Fintype.card (V i)

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


--THE ISSUE: I need to define the S i, because I'm currently using the V i both as the S i and
--any arbitrary member of X G p n, which means there's nothing to prove. So need to change
--these initial definitions.

--set of indices whose corresponding set has orbit not divisible by p
--currently assuming V is surjective, so given arbitrary P in X G p n is the same as arbitrary V i
def notdivset_orb {G I : Type*} [Group G] {p n : ℕ}
 [Fintype G] [Fintype I] [DecidableEq (X G p n)] (V : I → X G p n)
 := {k : I | ¬ (p ∣ Fintype.card (orbit G (V k)))}

--restrict this V to purely those with orbits not divisible by p
def orb_choice {G I : Type*} [Group G] {p n : ℕ} [Fintype G] [Fintype I] [DecidableEq (X G p n)]
 (V : I → X G p n) (i : notdivset_orb V) := V i

--there i at least one orbit not divisible by p
lemma notdivset_nonempty_orb {G I : Type*} [Group G] {p n : ℕ}
 [Fintype G] [Fintype I] [DecidableEq (X G p n)] (V : I → X G p n)
(hdiv : ¬ (p ∣ ∑ᶠ (i : I), Fintype.card (orbit G (V i)))) :
 ∃ (k : I), k ∈ notdivset_orb V := by
  have h₀ : ∃ (k : I), ¬ (p ∣ Fintype.card (orbit G (V k))) := by
    apply not_div_sum
    exact hdiv
  exact h₀

--if your orbit isn't divisible by p then your index is in the notdivset
lemma not_div_then_in_notdivset_orb {G I : Type*} [Group G] {p n : ℕ}
 [Fintype G] [Fintype I] [DecidableEq (X G p n)] (V : I → X G p n) :
 ∀ (i : I), ¬ (p ∣ Fintype.card (orbit G (V i))) → i ∈ notdivset_orb V := by
 unfold notdivset_orb
 exact fun i a ↦ a

--function that takes input an index and outputs the corresponding set
def select_orb_2 {G I : Type*} [Group G] {p n : ℕ} [Fintype G] [Fintype I]
 [DecidableEq (X G p n)] (V : I → X G p n) (j : notdivset_orb V) : X G p n := orb_choice V j

--check select_orb_2 is well defined, i.e. if inputs are the same then so are the outputs
lemma select_welldef1_orb_2 {G I : Type*} [Group G] {p n : ℕ}
 [Fintype G] [Fintype I] [DecidableEq (X G p n)] (V : I → X G p n)
  {U : I → Set ↑(X G p n)} (huv : ∀ (i : I), U i = orbit G (V i))
  (hdistinct : ∀ (i j : notdivset_orb V), orbit G (V i) = orbit G (V j) → V i = V j) :
  ∀ (i j : notdivset_orb V), i = j → select_orb_2 V i = select_orb_2 V j := by
  have h₀ : ∀ (i j : notdivset_orb V), i = j → U i = U j := by
    exact fun i j a ↦ congrArg U (congrArg Subtype.val a)
  have h₁ : ∀ (i : notdivset_orb V), U i = orbit G (V i) := by
    exact fun i ↦ huv ↑i
  have h₂ : ∀ (i j : notdivset_orb V), U i = U j → orbit G (V i) = orbit G (V j) := by
    intro x y
    rw [← h₁, ← h₁]
    exact fun a ↦ a
  have h₃ : ∀ (i j : notdivset_orb V), orbit G (V i ) = orbit G (V j) → V i = V j := by
    exact hdistinct
  have h₄ : ∀ (i : notdivset_orb V), V i = orb_choice V i := by
    exact fun i ↦ hdistinct i i (h₂ i i (h₀ i i rfl))
  have h₅ : ∀ (i j : notdivset_orb V), V i = V j → orb_choice V i = orb_choice V j := by
    intro x y
    rw [← h₄, ← h₄]
    exact fun a ↦ a
  intro x y eq
  apply h₅
  apply h₃
  apply h₂
  apply h₀
  exact eq

--rewriting claim one lemma to fit my notation
theorem claim_1_2_orb_2 {G I : Type*} [Group G] {p n : ℕ} [Fintype G]
 [Fintype I] [DecidableEq (X G p n)] (V : I → X G p n)
    (H : notdivset_orb V → Subgroup G)
    (hH : ∀ i, (H i : Set G) = (orb_choice V i).val)
    (i : notdivset_orb V) :
    (stabilizer G (orb_choice V i) : Set G) = (orb_choice V i).val := by
  ext g
  constructor
  · intro hg
    have h1_in_Si : (1 : G) ∈ (orb_choice V i).val := by
      rw [← hH i]
      exact OneMemClass.one_mem (H i)
    have : (orb_choice V i).val = (g • orb_choice V i).val := by
      ext x
      rw [hg]
    rw [this]
    exact ⟨1, h1_in_Si, mul_one g⟩

  · intro hg_in_Si
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, rfl⟩ := hx
      rw [← hH i] at hg_in_Si hs ⊢
      exact mul_mem hg_in_Si hs
    · intro hx
      use g⁻¹ * x
      constructor
      · rw [← hH i] at hg_in_Si hx ⊢
        exact mul_mem (inv_mem hg_in_Si) hx
      · group

--rewriting claim one lemma to fit my notation
theorem claim_1_2_subgroup_orb_2 {G I : Type*} [Group G] {p n : ℕ} [Fintype G]
 [DecidableEq (X G p n)] [Fintype I] (V : I → X G p n)
    (H : notdivset_orb V → Subgroup G)
    (hH : ∀ i, (H i : Set G) = (orb_choice V i).val)
    (i : notdivset_orb V) :
    H i = stabilizer G (orb_choice V i) := by
  have h := claim_1_2_orb_2 V H hH i
  apply SetLike.coe_injective
  rw [hH i, ← h]

--prove select_orb_2 is injective
lemma select_inj_orb_2 {G I : Type*} [Group G] {p n : ℕ}
 [Fintype G] [Fintype I] (V : I → X G p n) [DecidableEq (X G p n)] :
  ∀ (i j : notdivset_orb V), select_orb_2 V i = select_orb_2 V j
  → orbit G (orb_choice V i) = orbit G (orb_choice V j) := by
    exact fun i j a ↦ congrArg (orbit G) a


/-THIS LEMMA NEEDS REECE'S STUFF; CURRENT ERROR IS I ASSUME P IS A GROUP, WHICH ISN'T TRUE
lemma claim22_orb_2 {G I : Type*} [Group G] {p n : ℕ}
 [Fintype G] [Fintype I] [DecidableEq (X G p n)] (V : I → X G p n) (i : I)
 (H : Subgroup G) (hgrp : H = (V i).val)
 : stabilizer G (V i) = (V i).val := by
  ext g
  constructor
  ·
    intro hg
    have h1_in_P : (1 : G) ∈ (V i).val := by
      rw[← hgrp]
      exact OneMemClass.one_mem H
    have h₀ : (V i).val = (g • (V i)).val := by
      ext x
      rw [hg]
    rw[h₀]
    exact ⟨1, h1_in_P, mul_one g⟩
  ·
    intro hg_in_P
    ext x
    constructor
    ·
      intro hx
      obtain ⟨s, hs, rfl⟩ := hx
      rw [← hgrp] at hg_in_P hs ⊢
      exact mul_mem hg_in_P hs
    ·
      intro hx
      use g⁻¹ * x
      constructor
      · rw [← hgrp] at hg_in_P hx ⊢
        exact mul_mem (inv_mem hg_in_P) hx
      · group
-/
--prove orbit is not dividible by p for an arbitrary element of X G p n
lemma claim23 {G I : Type*} [Group G] {p n m : ℕ} [Fintype G] [Fintype I]
 [DecidableEq (X G p n)] (V : I → X G p n) (i : I)
    (hsame : stabilizer G (V i) = (V i).val) -- need Reece's bit to remove this assumption
    (hS : Fintype (stabilizer G (V i)))
    (hP : Fintype (V i))
    (hm : p.Coprime m)
    (P_order : Fintype.card (V i).val = p^n)
    (G_order : Fintype.card G = m * p^n)
    (hPrime : Nat.Prime p) : ¬ (p ∣ Fintype.card (orbit G (V i))) := by
    have h₀ : Fintype.card G
    = Fintype.card (orbit G (V i)) * Fintype.card (stabilizer G (V i)) := by
      convert orbit_stabilizer_theorem G (X G p n) (V i)
    have h₁ : Fintype.card (orbit G (V i))
    = Fintype.card G / Fintype.card (stabilizer G (V i)) := by
      refine Nat.eq_div_of_mul_eq_right ?_ ?_
      · exact Fintype.card_ne_zero
      apply Eq.symm
      rw [mul_comm]
      apply h₀
    have h₂ : Fintype.card (stabilizer G (V i)) = Fintype.card (V i) := by
      apply Fintype.card_congr'
      exact congrArg Subtype hsame --should be by reece's bit not hsame
    have h₃ : Fintype.card (orbit G (V i)) = m * p^n / p^n:= by
      rw [G_order] at h₁
      rw [h₂] at h₁
      rw [P_order] at h₁
      apply h₁
    have h₄ : m = m * p^n / p^n := by
     refine Nat.eq_div_of_mul_eq_right ?_ ?_
     ·
      refine pow_ne_zero n ?_
      exact Nat.Prime.ne_zero hPrime
     ·
      exact Nat.mul_comm (p ^ n) m
    have h₅ : Fintype.card (orbit G (V i)) = m := by
      rw [h₄]
      exact h₃
    have h₆ : p ∣ m ↔ ¬ p.Coprime m:= by
      apply Nat.Prime.dvd_iff_not_coprime hPrime
    have h₇ : ¬ p ∣ m ↔ p.Coprime m := by
      exact Decidable.not_iff_comm.mp (id (Iff.symm h₆))
    have h₈ : ¬ p ∣ m := by
      rw [h₇]
      exact hm
    have h₉ : ¬ p ∣ Fintype.card (orbit G (V i)) := by
      rw [h₅]
      exact h₈
    exact h₉

--thus V is in fact from notdivset, i.e. notdivset = I
lemma claim24_pt1 {G I : Type*} [Group G] {p n m : ℕ} [Fintype G] [Fintype I] [DecidableEq (X G p n)]
 (V : I → X G p n) (i : I)
    (hsame : stabilizer G (V i) = (V i).val) -- delete when we get Reece's bit
    (hS : Fintype (stabilizer G (V i)))
    (hP : Fintype (V i))
    (hm : p.Coprime m)
    (P_order : Fintype.card (V i).val = p^n)
    (G_order : Fintype.card G = m * p^n)
    (hPrime : Nat.Prime p) : i ∈ notdivset_orb V := by
    --(hsylp : ∀ (i : Fin r), Nat.card (S i) = p ^ n) :
    --∃ (j : notdivset_orb V), orbit G (V i) = orbit G (S j) := by
    have h₀ : ¬ (p ∣ Fintype.card (orbit G (V i))) := by
      convert claim23 V i hsame hS hP hm P_order G_order hPrime
    have h₁ : i ∈ notdivset_orb V := by
      exact h₀
    exact h₁
