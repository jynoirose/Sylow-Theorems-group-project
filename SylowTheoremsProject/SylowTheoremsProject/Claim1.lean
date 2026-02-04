import SylowTheoremsProject.OribitStabiliser


open MulAction
----
-- Finset.powersetCard in mathlib
-- define X(G,p,n) = {S ⊆ G | |S| = p ^ n}
def X (G : Type*) [Group G] (p n : ℕ) : Set (Set G) :=
  {S : Set G | Nat.card S = p ^ n}

-- G is a finite group
variable {G : Type*} [Group G] [Fintype G]

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
