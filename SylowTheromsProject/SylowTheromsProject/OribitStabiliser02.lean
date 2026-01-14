import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Index
import Mathlib.Data.Fintype.OfMap
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Algebra.Group.Subgroup.Pointwise

import Mathlib.Tactic

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
variable {G : Type*} [Group G] [Fintype G]

-- define leftmulaction G(X G p n) which is g • S = gS = {g * s | s ∈ S}
instance instMulActionGX : MulAction G (X G p n) where
  smul g S := ⟨(fun s => g * s) '' S.val, by
    have h := S.property
    simp only [X, Set.mem_setOf_eq] at h ⊢
    rw [Nat.card_image_of_injective]
    · exact h
    · exact mul_right_injective g⟩
  one_smul S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨x, hx, one_mul x⟩
  mul_smul g₁ g₂ S := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, rfl⟩ := hx
      use g₂ * s
      constructor
      · use s, hs
      · simp [mul_assoc]
    · intro hx
      obtain ⟨t, ht, rfl⟩ := hx
      obtain ⟨s, hs, rfl⟩ := ht
      use s, hs
      simp [mul_assoc]


-- Claim one : Stab_G(S_i) = S_i
theorem claim_1 {G : Type*} [Group G] {p n r : ℕ}
    (S : Fin r → X G p n)
    (H : Fin r → Subgroup G)
    (hH : ∀ i, (H i : Set G) = (S i).val)
    (i : Fin r) :
    (stabilizer G (S i) : Set G) = (S i).val := by
  ext g
  constructor
  · intro hg
    have h1_in_Si : (1 : G) ∈ (S i).val := by
      rw [← hH i]
      exact OneMemClass.one_mem (H i)
    have : (S i).val = (g • S i).val := by
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

-- Stab_G(S_i) = S_i is a subgroup
theorem claim_1_subgroup {G : Type*} [Group G] {p n r : ℕ}
    (S : Fin r → X G p n)
    (H : Fin r → Subgroup G)
    (hH : ∀ i, (H i : Set G) = (S i).val)
    (i : Fin r) :
    H i = stabilizer G (S i) := by
  have h := claim_1 S H hH i
  apply SetLike.coe_injective
  rw [hH i, ← h]

-- prove card of H i is p^n
lemma H_card_eq_pow {G : Type*} [Group G] [Fintype G] {p n : ℕ}
    (S : X G p n)
    (H : Subgroup G)
    (hH : (H : Set G) = S.val) :
    Nat.card H = p ^ n := by
  -- by prop of S, we have |S.val| = p^n
  have hS : Nat.card S.val = p ^ n := S.property
  -- because H set = S.val
  have : Nat.card (H : Set G) = Nat.card S.val := by
    rw [hH]
  rw [hS] at this
  exact this


-- if |H| = p^n，then H 是 p-group
lemma isPGroup_of_card_eq_prime_pow {G : Type*} [Group G] {p n : ℕ} [Fact p.Prime]
    (H : Subgroup G) [Fintype H] (h : Fintype.card H = p ^ n) : IsPGroup p H := by
  rw [IsPGroup.iff_card]
  exact ⟨n, by rw [Nat.card_eq_fintype_card]; exact h⟩


lemma fintype_card_of_nat_card {G : Type*} [Group G] [Fintype G] {p n : ℕ}
    (H : Subgroup G) [Fintype H] (h : Nat.card H = p ^ n) : Fintype.card H = p ^ n := by
  rw [← Nat.card_eq_fintype_card]
  exact h

-- main thorem of Claim one：H i (group version of S_i) is Sylow p-group

theorem H_is_sylow {G : Type*} [Group G] [Fintype G] {p n : ℕ}
    [hp : Fact p.Prime]
    (h_pn1_not_dvd : ¬ (p ^ (n + 1) ∣ Fintype.card G))
    (H : Subgroup G)
    (hH_card : Nat.card H = p ^ n) :
    IsPGroup p H ∧ ∀ (K : Subgroup G), IsPGroup p K → H ≤ K → H = K := by
  haveI : Fintype H := Fintype.ofFinite H
  have hH_fintype_card : Fintype.card H = p ^ n := fintype_card_of_nat_card H hH_card
  constructor

  · exact isPGroup_of_card_eq_prime_pow H hH_fintype_card

  · intro K hK_pgroup hHK
    by_contra hne
    have hH_lt_K : H < K := lt_of_le_of_ne hHK hne
    haveI : Fintype K := Fintype.ofFinite K
    have card_lt : Nat.card H < Nat.card K := by
      obtain ⟨k, hkK, hkH⟩ := SetLike.exists_of_lt hH_lt_K
      have h_le : Nat.card H ≤ Nat.card K := by
        apply Nat.card_mono (Set.toFinite _)
        exact SetLike.coe_subset_coe.mpr (le_of_lt hH_lt_K)
      have h_ne : Nat.card H ≠ Nat.card K := by
        intro heq
        have hsub : (H : Set G) ⊆ (K : Set G) := SetLike.coe_subset_coe.mpr (le_of_lt hH_lt_K)
        have hcard_eq : (H : Set G).encard = (K : Set G).encard := by
          rw [Set.encard_eq_coe_toFinset_card, Set.encard_eq_coe_toFinset_card]
          congr 1
          simp only [Set.toFinset_card, ← Nat.card_eq_fintype_card]
          exact heq
        have : (H : Set G) = (K : Set G) := by
          apply (Set.toFinite _).eq_of_subset_of_encard_le hsub
          exact le_of_eq hcard_eq.symm
        rw [SetLike.coe_set_eq] at this
        exact hkH (this ▸ hkK)
      exact Nat.lt_of_le_of_ne h_le h_ne

    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at card_lt

    obtain ⟨m, hm⟩ := hK_pgroup.exists_card_eq
    rw [Nat.card_eq_fintype_card] at hm

    have hK_dvd : Fintype.card K ∣ Fintype.card G := by
      have := Subgroup.card_subgroup_dvd_card K
      simp only [Nat.card_eq_fintype_card] at this
      exact this

    rw [hH_fintype_card, hm] at card_lt
    have hn_lt_m : n < m := (Nat.pow_lt_pow_iff_right hp.out.one_lt).mp card_lt

    have : p ^ (n + 1) ∣ Fintype.card G := by
      have h_n1_le_m : n + 1 ≤ m := hn_lt_m
      have h_pn1_dvd_pm : p ^ (n + 1) ∣ p ^ m := Nat.pow_dvd_pow p h_n1_le_m
      exact Nat.dvd_trans h_pn1_dvd_pm (hm ▸ hK_dvd)

    exact h_pn1_not_dvd this


lemma claim23 {G : Type*} [Group G] {p n r : ℕ} [Fintype G] [MulAction G (X G p n)]
 [DecidableEq (X G p n)]
    (P : X G p n)
    (hsame : (stabilizer G (P) : Set G) = (P).val)
    (hS : Fintype (stabilizer G (P))) :
    ∀ (P : X G p n), ¬ (p ∣ Fintype.card (orbit G P)) := by
    have h0 : Fintype.card G = Fintype.card (orbit G P) * Fintype.card (stabilizer G P) := by
      convert orbit_stabilizer_theorem G (X G p n) P
    sorry
