import Mathlib.GroupTheory.Sylow


import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Field.ZMod


import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Quot
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.Defs


import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Fintype.Defs
import Mathlib.GroupTheory.Index
import Mathlib.Data.Fintype.OfMap
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Algebra.Group.Subgroup.Pointwise


import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Restrict
import Init.Classical
import Mathlib.GroupTheory.Coset.Basic


----------------------------------------------------------------------------
/-NUMBER THEORY, steps 1-3 -/
----------------------------------------------------------------------------
open ZMod


-- from mathlib, p | p.choose i for 0 < i < p, p prime
theorem binomial_prime_mul {p i : ℕ} (hp : p.Prime) (hip : 0 < i ∧ i < p) : p ∣ (p.choose i) := by


  exact hp.dvd_choose_self hip.1.ne' hip.2


open Polynomial


-- proof that (1+X)^p=1+X^p mod p
theorem binomial_pow_p_mod_p {p : ℕ} (hp : p.Prime) :
    (1 + X : (ZMod p)[X]) ^ p = 1 + X ^ p := by


  -- binomial expansion
  rw [add_pow]
  -- split off the last term in the sum
  rw [Finset.sum_range_succ]
  simp
  -- split off the zero term of the sum
  have zero_in_range_p : 0 ∈ Finset.range p := Finset.mem_range.mpr hp.pos
  rw [Finset.sum_eq_sum_diff_singleton_add zero_in_range_p]
  ring_nf
  simp
  -- if f(x)=0 then Σf(x)=0
  apply Finset.sum_eq_zero
  intro n hn
  -- get conditions on n and simplify to get 0 < n < p
  have ⟨n_in_range_p, n_not_in_zero_set⟩ := Finset.mem_sdiff.mp hn
  apply Finset.mem_range.mp at n_in_range_p
  have n_not_zero : (n ≠ 0) := by
    apply List.ne_of_not_mem_cons n_not_in_zero_set
  have n_pos : (0 < n) := by
    exact Nat.zero_lt_of_ne_zero n_not_zero
  -- use binomial_prime_mul to show each term is zero when casted to (ZMod p)[X]
  have h_div : p ∣ (p.choose n) := by
    apply binomial_prime_mul hp
    exact ⟨n_pos, n_in_range_p⟩
  have h_zero : (p.choose n : ZMod p) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact h_div
  rw [← Polynomial.C_eq_natCast]
  rw [h_zero]
  simp


-- proof that (1+X)^p^n=1+X^p^n mod p
theorem binomial_pow_p_n_mod_p {p n : ℕ} {hp : p.Prime} :
    (1 + X : (ZMod p)[X]) ^ p ^ n = 1 + X ^ p ^ n := by


  -- get binomial_pow_p_mod_p as a proposition
  have composed_lemma := binomial_pow_p_mod_p hp
  induction n with
  | zero =>
    simp
  | succ d hd =>
    rw [pow_succ, pow_mul]
    -- the inductive step falls out when composing binomial_pow_p_mod_p with X^p^d
    apply_fun (fun f => f.comp (X ^ p ^ d)) at composed_lemma
    simp at composed_lemma
    rw [hd, composed_lemma, pow_mul]


-- proof that (1+X)^p^n=1+X^p^n mod p
theorem binomial_pow_p_n_m_mod_p {p n m : ℕ} {hp : p.Prime} :
    (1 + X : (ZMod p)[X]) ^ (p ^ n * m) = (1 + X ^ p ^ n) ^ m := by


  -- raise both sides of binomial_pow_p_n_mod_p to the power of m
  have composed_lemma := congr_fun (congr_arg HPow.hPow (@binomial_pow_p_n_mod_p p n hp)) m
  rw [← pow_mul] at composed_lemma
  exact composed_lemma


-- proof that p^n * m choose p^n *j = m choose j mod p
theorem choose_ignores_pn_mod_p {p n m j : ℕ} {hp : p.Prime} :
    ((p^n * m).choose (p^n * j) : ZMod p) = m.choose j := by


  -- get binomial_pow_p_n_m_mod_p as a proposition
  have polynomial_equality := @binomial_pow_p_n_m_mod_p p n m hp
  -- two polynomials are equal iff their coefficients are equal for every power of X
  rw [ext_iff] at polynomial_equality
  specialize polynomial_equality (p^n * j)
  -- extract the binomial coefficient
  rw [coeff_one_add_X_pow] at polynomial_equality
  -- expand p sends x^n to x^np. i expand by p^n so i can work with the simpler (1+X)^j
  have h_expand : (1 + X ^ (p ^ n) : (ZMod p)[X]) = (expand (ZMod p) (p ^ n)) (1 + X) := by
    simp
  rw [h_expand, ← map_pow, coeff_expand_mul'] at polynomial_equality
  · rw [coeff_one_add_X_pow] at polynomial_equality
    exact polynomial_equality
  apply pow_pos
  exact hp.pos


-- proof that p^n * m choose p^n = m mod p
theorem binomial_prime_pow_mul {p n m : ℕ} (hp : p.Prime) :
    ((p^n * m).choose (p^n) : ZMod p) = m := by


  -- simply take choose_ignores_pn_mod_p with j = 1
  have binomial_equality := @choose_ignores_pn_mod_p p n m 1 hp
  simp at binomial_equality
  exact binomial_equality


-- proof that if m and p are coprime, then m is nonzero
theorem m_coprime_nonzero_mod_p (m p : ℕ) (hp : p.Prime) (h : Nat.Coprime m p) :
    (m ≠ (0 : ZMod p)) := by


  intro h0
  have h_div : p ∣ m := by
    exact (natCast_eq_zero_iff m p).mp h0
  have h_gcd := Nat.gcd_eq_right h_div
  rw [Nat.coprime_iff_gcd_eq_one, h_gcd] at h
  have : (p ≠ 1) := Nat.Prime.ne_one hp
  contradiction


-- define X as the set of all subsets of group G with cardinality p^n
def Xsubsets (G : Type*) [Group G] [Fintype G] (p n : ℕ) : Finset (Finset G) :=
  Finset.powersetCard (p^n) Finset.univ


-- prove that the size of Xsubsets is p^n * m choose p ^ n
theorem Xsubsets_card (G : Type*) [Group G] [Fintype G] (p n m : ℕ)
                      (hcard : Fintype.card G = p ^ n * m) :
    (Xsubsets G p n).card = (p^n * m).choose (p^n) := by


  rw [Xsubsets, Finset.card_powersetCard, Finset.card_univ, hcard]


-- prove that the size of Xsubsets is m mod p
theorem Xsubsets_card_mod (G : Type*) [Group G] [Fintype G] (p n m : ℕ)
                          (hp : p.Prime)
                          (hcard : Fintype.card G = p ^ n * m) :
    (Xsubsets G p n).card = (m : ZMod p) := by


    rw [@Xsubsets_card G _ _ p n m]
    · rw [@binomial_prime_pow_mul p n m hp]
    exact hcard


-- prove that p does not divide the cardinality of Xsubsets
theorem p_not_dvd_card_Xsubsets (G : Type*) [Group G] [Fintype G] (p n m : ℕ)
                                (hp : p.Prime) (hcoprime : Nat.Coprime m p)
                                (hcard : Fintype.card G = p ^ n * m) :
    ¬(p ∣ (Xsubsets G p n).card) := by


  intro h
  rw [← ZMod.natCast_eq_zero_iff] at h
  rw [Xsubsets_card_mod G p n m hp hcard] at h
  have m_nonzero := @m_coprime_nonzero_mod_p m p hp hcoprime
  contradiction


------------------------------------------------------------------------------
/-ORBIT STABILISER-/
------------------------------------------------------------------------------
open MulAction


-- The following lemma states that orbits are finite
-- G is a finite group that can act on X, x is an element in X
-- The conclusion to prove is that the set Orb_G(X) is finite
lemma orbit_finite {G X' : Type*} [Group G] [MulAction G X'] [Fintype G] (x : X') :
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
noncomputable instance orbit_fintype {G X' : Type*} [Group G] [MulAction G X']
    [Fintype G] (x : X') : Fintype (orbit G x) :=
  (orbit_finite x).fintype




-- Define orbitMap: G/Stab(x) → Orbit(x), we need to prove this definition is well-defined
def orbitMap {G : Type*} [Group G] {X' : Type*} [MulAction G X'] (x : X') :
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
lemma orbitMap_injective_on {G : Type*} [Group G] {X' : Type*} [MulAction G X'] (x : X') :
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
lemma orbitMap_surjective_on {G : Type*} [Group G] {X' : Type*} [MulAction G X'] (x : X') :
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
lemma orbitMap_bijective {G : Type*} [Group G] {X' : Type*} [MulAction G X'] (x : X') :
  Function.Bijective (orbitMap (G := G) (X' := X') x) := by
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
  (X' : Type*) [MulAction G X'] [DecidableEq X']
  (x : X') :
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
        rw [Fintype.card_of_bijective (orbitMap_bijective (G := G) (X' := X') x)]




-- Below we prove some related properties and corollaries of the orbit-stabilizer theorem




-- Corollary 2.17 (i): Any two orbits are either completely the same or completely disjoint
theorem orbit_disjoint_or_eq {G X' : Type*} [Group G] [MulAction G X'] (x y : X') :
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
theorem orbits_partition {G X' : Type*} [Group G] [MulAction G X'] :
    (Set.range (orbit G : X' → Set X')).PairwiseDisjoint id := by
  intro A hA B hB hAB -- Introduce sets A and B as elements in the orbits, with A ≠ B
  rcases hA with ⟨x, rfl⟩ -- Write set A as A = orbit G x
  rcases hB with ⟨y, rfl⟩ -- Write set B as B = orbit G y
  -- Apply the previously proved theorem: orbits are either equal or disjoint
  have h := orbit_disjoint_or_eq (G := G) (X' := X') x y
  rcases h with h_eq | h_disj
  · -- If the orbits are equal, this contradicts A ≠ B
    contradiction
  · -- So they must be disjoint
    exact h_disj




-- Corollary 2.17 (iii): |Orb(x)| divides |G|
theorem orbit_card_dvd_group_card
    {G X' : Type*} [Group G] [Fintype G] [MulAction G X'] [DecidableEq X'] (x : X') :
    Fintype.card (orbit G x) ∣ Fintype.card G := by
  have h := orbit_stabilizer_theorem G X' x -- Apply the orbit-stabilizer theorem
  rw [h]
  simp [dvd_mul_right] -- Use a ∣ a * b to directly obtain the result


----------------------------------------------------------------------------
/-CLAIM 1, steps 11-17-/
-----------------------------------------------------------------------------
open MulAction
----
-- Finset.powersetCard in mathlib
-- define X(G,p,n) = {S ⊆ G | |S| = p ^ n}
def X' (G : Type*) [Group G] (p n : ℕ) : Set (Set G) :=
  {S : Set G | Nat.card S = p ^ n}


-- G is a finite group
variable {G : Type*} [Group G] [Fintype G]


-- define leftmulaction G(X G p n) which is g • S = gS = {g * s | s ∈ S}
instance instMulActionGX : MulAction G (X' G p n) where


  -- Define the scalar multiplication: g • S is obtained by left-multiplying each element of S by g
  smul g S := ⟨(fun s => g * s) '' S.val, by
    -- Get the property of S (S satisfies the defining condition of X)
    have h := S.property
    simp only [X', Set.mem_setOf_eq] at h -- Simplify in hypothesis h
    simp only [X', Set.mem_setOf_eq] -- Simplify in goal
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
    (S : Fin r → X' G p n)
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
    (S : Fin r → X' G p n)
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
    (S : X' G p n)
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
-------------------------------------------------------------------------------------
/-DEFINING THE SET OF SYLOW P SUBGROUPS-/
-------------------------------------------------------------------------------------
def isPSubgroup {G : Type _} [Group G] [Fintype G] (p : ℕ)
    (H : Subgroup G) : Prop :=
∃ n : ℕ, Nat.card (H : Type _) = p ^ n


def isSylow {G : Type _} [Group G] [Fintype G] (p : ℕ)
    (P : Subgroup G) : Prop :=
∃ n : ℕ,
  Nat.card (P : Type _) = p ^ n ∧
  p ^ n ∣ Nat.card G ∧
  ¬ p ^ (n+1) ∣ Nat.card G


def Syl_p (G : Type _) [Group G] [Fintype G] (p : ℕ) :=
  { P : Subgroup G // isSylow p P }

-------------------------------------------------------------------------------------
/-DEFINING THE Si, OUR ORBIT REPRESENTATIVES THAT PARTITION X, steps 5-8 -/
-------------------------------------------------------------------------------------
open Fintype
open Finset
universe u v


variable {G : Type*} [Group G] [Fintype G]
variable {p n : ℕ} [Fact p.Prime]


/--Step 5 for every `S : X' G p n`, there exists `T` in the orbit of `S` such that `1 ∈ T`-/
lemma step5_exists_one_mem_orbit (S : (X' G p n)) :
    ∃ T : (X' G p n), T ∈ orbit G S ∧ (1 : G) ∈ (T : Set G) := by
  classical


  -- `S ∈ X' G p n` means `|S| = p^n`
  have hNat : Nat.card ((S : Set G)) = p ^ n := by
    simpa [X'] using (S.property)


  -- Put a Fintype on the underlying set so we can use Fintype.card lemmas
  letI : Fintype (↑(S : Set G)) := Fintype.ofFinite (↑(S : Set G))


  -- Convert Nat.card to Fintype.card
  have hcard : Fintype.card (↑(S : Set G)) = p ^ n := by
    simpa [Nat.card_eq_fintype_card] using hNat


  -- p is prime so p > 0
  have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
  -- so S has positive size and is nonempty
  have hpos : 0 < Fintype.card (↑(S : Set G)) := by
    simpa [hcard] using (pow_pos hp0 n)


  -- choose s ∈ S
  obtain ⟨s⟩ : Nonempty (↑(S : Set G)) := Fintype.card_pos_iff.1 hpos


  -- Let g = s⁻¹, and set T = g • S; then 1 ∈ T because g*s = 1.
  let g : G := (s : G)⁻¹
  refine ⟨g • S, ?_, ?_⟩
  · exact ⟨g, rfl⟩
  ·
    refine ⟨(s : G), s.property, ?_⟩
    simp [g]


/--Step 6-/
lemma orbit_eq_of_mem
  {G X' : Type*} [Group G] [MulAction G X']
  {S T : X'} (h : T ∈ orbit G S) :
  orbit G T = orbit G S := by
  --Orbits are either equal or disjoint
  have h' := orbit_disjoint_or_eq (G := G) (X' := X') T S
  cases h' with
  --They are equal and we are done
  | inl hEq =>
      exact hEq
  --Or they are disjoint
  | inr hDisj =>
      -- Show T is in the orbit of T
      have hTT : T ∈ orbit G T := by
        exact ⟨(1 : G), by simp⟩
      -- contradiction: T is in both disjoint orbits
      have : False := (Set.disjoint_left.1 hDisj) hTT h
      exact False.elim this


/-- Step 7 The type of distinct orbits, i.e., the quotient of X by the orbit relation -/


def OrbitIndex (G X' : Type*) [Group G] [MulAction G X'] :=
  Quotient (MulAction.orbitRel G X')


/-- The family of distinct orbits, indexed without repetition. -/
def OrbitFamily
  {G X' : Type*} [Group G] [MulAction G X'] :
  OrbitIndex G X' → Set X' :=
  Quotient.lift
    (fun x : X' => orbit G x) -- representative orbit
    (by
      intro a b hab
      -- `hab : ∃ g0, g0 • b = a`  (orbit relation)
      rcases hab with ⟨g0, hg0⟩
      ext x
      constructor
      ·  --Forward directionx - `x ∈ orbit G a → x ∈ orbit G b`
        rintro ⟨g, rfl⟩
        refine ⟨g * g0, ?_⟩
        -- `(g * g0) • b = g • (g0 • b) = g • a`
        simp [mul_smul, hg0]
      · -- Backward direction - `x ∈ orbit G b → x ∈ orbit G a`
        rintro ⟨g, rfl⟩
        refine ⟨g * g0⁻¹, ?_⟩
        -- rewrite `g0⁻¹•a = b` using hg0
        have hb : g0⁻¹ • a = b := by
          have h1 : g0⁻¹ • (g0 • b) = g0⁻¹ • a :=
            congrArg (fun t => g0⁻¹ • t) hg0
          -- simplify left side to b
          -- `h1 : b = g0⁻¹ • a`, so symm gives `g0⁻¹ • a = b`
          have : b = g0⁻¹ • a := by
            simpa [inv_smul_smul] using h1
          simpa using this.symm
        -- now substitute hb
        simp [mul_smul, hb])


/-- Step 7 - range OrbitFamily = range orbit -/
lemma OrbitFamily_surjective
  {G X' : Type*} [Group G] [MulAction G X'] :
  Set.range (OrbitFamily (G := G) (X' := X'))
    = Set.range (orbit G : X' → Set X') := by
  classical
  ext A
  constructor
  -- OrbitFamily side → orbit side
  · rintro ⟨i, rfl⟩
    -- reduce quotient index to representative
    refine Quotient.inductionOn i (fun x => ?_)
    exact ⟨x, rfl⟩


  -- Orbit side → OrbitFamily side
  · rintro ⟨x, rfl⟩
    refine ⟨Quotient.mk _ x, ?_⟩
    rfl


/--Distinct orbit indices give disjoint orbits --/
lemma OrbitFamily_pairwise_disjoint
  {G X' : Type*} [Group G] [MulAction G X'] :
  Pairwise (fun i j =>
    Disjoint (OrbitFamily (G := G) (X':= X') i)
             (OrbitFamily (G := G) (X' := X') j)) := by
  classical
  intro i j hij
  -- push inequality inside quotient induction
  revert hij
  refine Quotient.inductionOn₂ i j (fun a b => ?_)
  intro hij
  -- now hij : ⟦a⟧ ≠ ⟦b⟧


  -- use orbit disjoint-or-equal lemma
  have h := orbit_disjoint_or_eq (G := G) (X' := X') a b
  cases h with


  | inr hDisj =>
      -- Disjoint case - just unfold OrbitFamily on mk's
      simpa [OrbitFamily] using hDisj


  | inl hEq =>
      -- Equal-orbit case - contradict hij by proving ⟦a⟧ = ⟦b⟧
      exfalso
      apply hij
      apply Quotient.sound


      -- From hEq we have b ∈ orbit G a
      have hb : b ∈ orbit G a := by
        -- b ∈ orbit G b always
        have : b ∈ orbit G b := mem_orbit_self b
        -- transport along equality of orbits
        simpa [hEq] using this


      rcases (mem_orbit_iff.mp hb) with ⟨g, hg⟩
      refine ⟨g⁻¹, ?_⟩


      --Invert the action equation
      have : g⁻¹ • b = a := by
        have h1 := congrArg (fun t => g⁻¹ • t) hg
        have h2 : a = g⁻¹ • b := by
          simpa [inv_smul_smul] using h1
        exact h2.symm
      exact this


open MulAction


section ChooseSi


variable {G : Type*} [Group G] [Fintype G]
variable {p n : ℕ} [Fact p.Prime]


/-- Step 5 every orbit in OrbitFamily contains some T with `1 ∈ T` -/
lemma step5_index_exists_one
  (i : OrbitIndex G (X' G p n)) :
    ∃ T : X' G p n,
      T ∈ OrbitFamily (G := G) (X' := X' G p n) i ∧
      (1 : G) ∈ (T : Set G) := by
  classical
  refine Quotient.inductionOn i (fun S => ?_)
  rcases step5_exists_one_mem_orbit (G := G) (p := p) (n := n) S with
    ⟨T, hT, h1⟩
  refine ⟨T, ?_, h1⟩
  -- OrbitFamily ⟦S⟧ = orbit G S by definition
  simpa [OrbitFamily] using hT




/-- The explicit representative Si chosen from each orbit, with the property that 1 ∈ Si -/
noncomputable def S_i
  (i : OrbitIndex G (X' G p n)) : X' G p n :=
  Classical.choose
    (step5_index_exists_one (G := G) (p := p) (n := n) i)




/-- Si lies in the orbit indexed by i-/
lemma S_i_mem_OrbitFamily
  (i : OrbitIndex G (X' G p n)) :
    S_i (G := G) (p := p) (n := n) i
      ∈ OrbitFamily (G := G) (X' := X' G p n) i :=
  (Classical.choose_spec
    (step5_index_exists_one (G := G) (p := p) (n := n) i)).1




/-- By construction, `1 ∈ Si`. -/
lemma one_mem_S_i
  (i : OrbitIndex G (X' G p n)) :
    (1 : G) ∈
      (S_i (G := G) (p := p) (n := n) i : Set G) :=
  (Classical.choose_spec
    (step5_index_exists_one (G := G) (p := p) (n := n) i)).2


end ChooseSi




/-- Every OrbitFamily i is finite when G is finite. -/
lemma OrbitFamily_finite
  (i : OrbitIndex G (X' G p n)) :
  (OrbitFamily (G := G) (X' := X' G p n) i).Finite := by
  classical
  refine Quotient.inductionOn i (fun S => ?_)
  -- OrbitFamily ⟦S⟧ = orbit G S
  simpa [OrbitFamily] using (orbit_finite (G := G) (X' := X' G p n) S)


/-- The union of all distinct orbits (OrbitFamily) is the whole universe. -/
lemma iUnion_OrbitFamily_eq_univ :
  (⋃ i : OrbitIndex G (X' G p n),
      OrbitFamily (G := G) (X' := X' G p n) i) = (Set.univ : Set (X' G p n)) := by
  classical
  ext x
  constructor
  · intro _
    trivial
  · intro _
    refine Set.mem_iUnion.mpr ?_
    refine ⟨Quotient.mk _ x, ?_⟩
    simpa [OrbitFamily] using (mem_orbit_self (G := G) x)


variable {G : Type*} [Group G] [Fintype G]
variable {p n : ℕ} [Fact p.Prime]
/-- `OrbitFamily i` is the same orbit as the chosen representative `S_i i`. -/
lemma OrbitFamily_eq_orbit_Si
  (i : OrbitIndex G (X' G p n)) :
  OrbitFamily (G := G) (X' := X' G p n) i
    =
  orbit G (S_i (G := G) (p := p) (n := n) i) := by
  classical
  refine Quotient.inductionOn i (fun S => ?_)
  -- S_i ⟦S⟧ ∈ OrbitFamily ⟦S⟧ = orbit G S
  have hmem :
      S_i (G := G) (p := p) (n := n) (Quotient.mk _ S)
        ∈ orbit G S := by
    simpa [OrbitFamily] using
      (S_i_mem_OrbitFamily (G := G) (p := p) (n := n) (Quotient.mk _ S))
  -- hence its orbit equals orbit G S
  have horb :
      orbit G (S_i (G := G) (p := p) (n := n) (Quotient.mk _ S))
        =
      orbit G S :=
    orbit_eq_of_mem (G := G) (X' := X' G p n) hmem
  -- OrbitFamily ⟦S⟧ = orbit G S
  simpa [OrbitFamily, horb] using horb.symm
------------------------------------------------------------------------------
/-BIJECTIVITY STATEMENTS, steps 9 & 10-/
--------------------------------------------------------------------------------
/-bijectivity statements surrounding sums-/
variable {α : Type*} (I : Finset α) (p : ℕ)


def icard {U : Type u} {I : Type v} [Fintype I]
{V : I → Set U} (i : I) (hV : ∀ (i : I), Fintype (V i))
: ℕ := Fintype.card (V i)


--skeleton (9), cardinality of disjoint union is sum of cardinatilities 
theorem card_union_disj
  {U : Type*} {I : Type*} [Fintype I]
  {V : I → Set U}
  (hV : ∀ i : I, (V i).Finite)
  (hdisj : Pairwise (fun i j => Disjoint (V i) (V j))) :
  (⋃ i : I, V i).ncard = ∑ᶠ i : I, (V i).ncard := by
  classical
  exact Set.ncard_iUnion_of_finite hV hdisj


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
------------------------------------------------------------------------------
/-CLAIM 2, steps 18-33 
The first step of this section is to define a function from {Orbit G Si ∣ p ∤ |Orbit G Si|} to Si.
Unfortunately we ran out of time to define this function correctly (I tried to work around it, but the proof ultimately doesn't hold up.-/
------------------------------------------------------------------------------
--define the set of indices whose corresponding sets have orbits not divisible by p
def notdivset_orb {G I : Type*} [Group G] {p n : ℕ}
 [Fintype G] [Fintype I] (V : I → X' G p n)
 := {k : I | ¬ (p ∣ Fintype.card (orbit G (V k)))}


 --there is at least one orbit not divisible by p
lemma notdivset_nonempty_orb {G I : Type*} [Group G] {p n : ℕ}
 [Fintype G] [Fintype I] [DecidableEq (X' G p n)] (V : I → X' G p n)
(hdiv : ¬ (p ∣ ∑ᶠ (i : I), Fintype.card (orbit G (V i)))) :
 ∃ (k : I), k ∈ notdivset_orb V := by
  have h₀ : ∃ (k : I), ¬ (p ∣ Fintype.card (orbit G (V k))) := by
    apply not_div_sum
    exact hdiv
  exact h₀


--if your orbit isn't divisible by p then your index is in notdivset_orb
lemma not_div_then_in_notdivset_orb {G I : Type*} [Group G] {p n : ℕ}
 [Fintype G] [Fintype I] [DecidableEq (X' G p n)] (V : I → X' G p n) :
 ∀ (i : I), ¬ (p ∣ Fintype.card (orbit G (V i))) → i ∈ notdivset_orb V := by
 unfold notdivset_orb
 exact fun i a ↦ a


--restrict V to indices with corresponding orbits not divisible by p
def orb_choice {G I : Type*} [Group G] {p n : ℕ} [Fintype G] [Fintype I] [DecidableEq (X' G p n)]
 (V : I → X' G p n) (i : notdivset_orb V) := V i


/-We want every member of X' G p n to be Vi for some i. This is sorry'd out as redefining the Vi's as a surjective function required excessive reworking of existing code-/
lemma v_is_surj {G I : Type*} [Group G] {p n : ℕ}
 [Fintype G] [Fintype I] [DecidableEq (X' G p n)] (J : {P : Subgroup G // Nat.card P = p^n})
 (V : I → X' G p n) : ∃ (i : I), J = (V i).val := by
 sorry


 --rewriting claim_1_seteq lemma to use this newly defined notation
theorem claim_1_seteq_notation {G I : Type*} [Group G] {p n : ℕ} [Fintype G]
 [Fintype I] [DecidableEq (X' G p n)] (V : I → X' G p n)
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


--rewriting claim_1_subgroup lemma to fit my notation
theorem claim_1_subgroup_notation {G I : Type*} [Group G] {p n : ℕ} [Fintype G]
 [DecidableEq (X' G p n)] [Fintype I] (V : I → X' G p n)
    (H : notdivset_orb V → Subgroup G)
    (hH : ∀ i, (H i : Set G) = (orb_choice V i).val)
    (i : notdivset_orb V) :
    H i = stabilizer G (orb_choice V i) := by
  have h := claim_1_seteq_notation V H hH i
  apply SetLike.coe_injective
  rw [hH i, ← h]




def leftCoset (H : Subgroup G) (g : G) : Set G := { x | g⁻¹ * x ∈ H }


lemma leftCoset_eq_of_mem {H : Subgroup G} {g k : G}
  (hk : k ∈ leftCoset H g) :
  leftCoset H g = leftCoset H k := by


  ext x
  constructor


  · intro hx
    have hxH : g⁻¹ * x ∈ H := hx
    -- hk has type: k ∈ leftCoset H g - needs to be ufolded to be used
    have h_inv : (g⁻¹ * k)⁻¹ ∈ H := H.inv_mem hk
    --Closure of H under multiplication
    have hx' : (g⁻¹ * k)⁻¹ * (g⁻¹ * x) ∈ H := H.mul_mem h_inv hxH
    -- simplifies (g⁻¹ * k)⁻¹ * (g⁻¹ * x) to k⁻¹ * x
    simpa [leftCoset, mul_assoc] using hx'


  · intro hx
    have hxH : k⁻¹ * x ∈ H := hx
    -- hk has type: k ∈ leftCoset H g - needs to be ufolded to be used
    have hx' : (g⁻¹ * k) * (k⁻¹ * x) ∈ H := H.mul_mem hk hxH
    simpa [leftCoset, mul_assoc] using hx'


--This is a modfiedied version of Lemma 1.15 in the MA3K4 lecture notes and used to prove step 22 in claim 2
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


/-This lemma states that if a subgroup H is equal to the orbit of an element V i, then the stabilizer of V i is equal to H
The proof follows the notes in principal which uses Lemma 1.15 above, but due to type issues most of the proof is exchanging between H and (V i).val-/
lemma claim22 {G I : Type*} [Group G] {p n : ℕ}
 [Fintype G] [Fintype I] [DecidableEq (X' G p n)] (V : I → X' G p n) (i : I)
 (H : Subgroup G) (hgrp : H = (V i).val)
 : stabilizer G (V i) = (V i).val := by
  classical


  -- First helper - left-multiplying every element of H by g gives exactly the left coset {x | g⁻¹ * x ∈ H}
  have image_eq_leftCoset (H : Subgroup G) (g : G) :
      (fun s : G => g * s) '' (H : Set G) = leftCoset H g := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      -- if x = g*s with s ∈ H, then g⁻¹*x = s ∈ H
      simpa [leftCoset, mul_assoc] using hs
    · intro hx
      -- if g⁻¹*x ∈ H, just set s = g⁻¹*x so that x = g*s
      refine ⟨g⁻¹ * x, hx, ?_⟩
      simp [mul_assoc]


  -- Second helper - the coset with 1 is just H itself
  have leftCoset_one (H : Subgroup G) : leftCoset H (1 : G) = (H : Set G) := by
    ext x
    simp [leftCoset]


  -- Rewrite the hypothesis so we can freely swap (V i).val with H
  have hgrp_set : (H : Set G) = (V i).val := by
    simpa using hgrp


  -- We can now check membership to prove equality
  ext g
  constructor


  · intro hg
    -- hg means g fixes the set V i under the group action
    have hg_eq : g • V i = V i := hg


    -- Turn that equality in X G p n into equality of actual sets
    have hg_set : (g • V i).val = (V i).val :=
      congrArg Subtype.val hg_eq


    -- The action is defined using left-multiplication and image
    have himage :
      (fun s : G => g * s) '' (V i).val = (V i).val := by
      simpa [instMulActionGX] using hg_set


    -- Replace (V i).val by H
    have : (fun s : G => g * s) '' (H : Set G) = (H : Set G) := by
      simpa [hgrp_set] using himage


    -- Translate this into a statement about cosets
    have hcoset : leftCoset H g = leftCoset H (1 : G) := by
      calc
        leftCoset H g
        -- First rewrite it as the image under left-multiplication
            = (fun s : G => g * s) '' (H : Set G) := by
                symm; simpa using (image_eq_leftCoset H g)
        -- Then use the fact we already proved: g * H = H
        _ = (H : Set G) := this
        -- Finally rewrite H itself as the coset with 1
        _ = leftCoset H (1 : G) := by
                symm; exact leftCoset_one H


    -- Now use your coset lemma to get membership in H
    have hgH : g ∈ leftCoset H (1 : G) := by
      apply (Eq_of_cosets (H := H) (g := (1 : G)) (k := g)).2
      simpa [eq_comm] using hcoset


    -- leftCoset H 1 is just H, so we’re done
    have : g ∈ (H : Set G) := by
      simpa [leftCoset] using hgH
    simpa [hgrp_set] using this


  · intro hg_in_V
    -- Start by rewriting membership in `(V i).val` as membership in H
    have hgH : g ∈ (H : Set G) := by
      simpa [hgrp_set] using hg_in_V


    -- From `g ∈ H` we get `g⁻¹ ∈ H`, which means 1 is in the coset of g
    have h1 : (1 : G) ∈ leftCoset H g := by
      have : g⁻¹ ∈ H := H.inv_mem hgH
      simpa [leftCoset] using this


    -- If 1 is in the coset of g, the two cosets are equal
    have hcoset : leftCoset H g = leftCoset H (1 : G) :=
      leftCoset_eq_of_mem (H := H) (g := g) (k := (1 : G)) h1


    -- Turn coset equality back into an equality of images
    have himageH : (fun s : G => g * s) '' (H : Set G) = (H : Set G) := by
      calc
        (fun s : G => g * s) '' (H : Set G)
            = leftCoset H g := by
                simpa using (image_eq_leftCoset H g)
        _ = leftCoset H (1 : G) := hcoset
        _ = (H : Set G) := by
                simpa using (leftCoset_one H)


    -- Swap H back to `(V i).val`
    have himageV :
      (fun s : G => g * s) '' (V i).val = (V i).val := by
      simpa [hgrp_set] using himageH


    -- Finally lift this set equality back to equality in `X G p n`
    apply (show g • V i = V i from ?_)
    apply Subtype.ext
    simpa [instMulActionGX] using himageV


  --prove orbit is not divisible by p for an arbitrary element of X G p n
lemma claim23 {G I : Type*} [Group G] {p n m : ℕ} [Fintype G] [Fintype I]
 [DecidableEq (X' G p n)] (V : I → X' G p n) (i : I)
    (hS : Fintype (stabilizer G (V i)))
    (hP : Fintype (V i))
    (hm : p.Coprime m)
    (H : Subgroup G) (hgrp : H = (V i).val)
    (P_order : Fintype.card (V i).val = p^n)
    (G_order : Fintype.card G = m * p^n)
    (hPrime : Nat.Prime p) : ¬ (p ∣ Fintype.card (orbit G (V i))) := by
    have h00 : stabilizer G (V i) = (V i).val := by
      apply claim22 V i H hgrp
    have h₀ : Fintype.card G
    = Fintype.card (orbit G (V i)) * Fintype.card (stabilizer G (V i)) := by
      convert orbit_stabilizer_theorem G (X' G p n) (V i)
    have h₁ : Fintype.card (orbit G (V i))
    = Fintype.card G / Fintype.card (stabilizer G (V i)) := by
      refine Nat.eq_div_of_mul_eq_right ?_ ?_
      · exact Fintype.card_ne_zero
      apply Eq.symm
      rw [mul_comm]
      apply h₀
    have h₂ : Fintype.card (stabilizer G (V i)) = Fintype.card (V i) := by
      apply Fintype.card_congr'
      exact congrArg Subtype h00
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


--thus any p subgroup has p ∤ |orbit G Vi|, so in fact every i in I
--is in notdivset_orb V, i.e. notdivset_orb V = I
lemma claim24_pt1 {G I : Type*} [Group G] {p n m : ℕ}
[Fintype G] [Fintype I] [DecidableEq (X' G p n)]
 (V : I → X' G p n) (i : I)
    (hS : Fintype (stabilizer G (V i)))
    (hP : Fintype (V i))
    (hm : p.Coprime m)
    (H : Subgroup G) (hgrp : H = (V i).val)
    (P_order : Fintype.card (V i).val = p ^ n)
    (G_order : Fintype.card G = m * p ^ n)
    (hPrime : Nat.Prime p) : i ∈ notdivset_orb V := by
    --(hsylp : ∀ (i : Fin r), Nat.card (S i) = p ^ n) :
    --∃ (j : notdivset_orb V), orbit G (V i) = orbit G (S j) := by
    have h00 : stabilizer G (V i) = (V i).val := by
      apply claim22 V i H hgrp
    have h₀ : ¬ (p ∣ Fintype.card (orbit G (V i))) := by
      convert claim23 V i hS hP hm H hgrp P_order G_order hPrime
    have h₁ : i ∈ notdivset_orb V := by
      exact h₀
    exact h₁




/-currently, the function V has image in X G p n, i.e. subsets of size
p^n. We want to consider _subgroups_ of size p^n. So we want every Vi to be
considered as a member of X' G p n in order to use the group action, which is defined on X' G p n, but also considered a subgroup in order to use subgroup properties like (1 : G) ∈ P etc


This lemma matches each subset Vi with a subgroup Wi. When we need the subgroup properties, we switch to using the Wi, and when we need properties of the group action, we switch back to Vi. It is sorry'd out as it is not group theory, and finding an alternative way to switch between subgroup and subset proved difficult and time consuming-/
lemma Wi_is_Vi {G I : Type*} [Group G] {p n : ℕ} [Fintype G] [Fintype I] [DecidableEq (X' G p n)]
 (V : I → X' G p n) (W : notdivset_orb V → Subgroup G) :
 ∀ (i : notdivset_orb V), W i = (V i).val := sorry


 /-So we now have each Vi is both a member of X' G p n and a subgroup
 of G. This is equivalent to being a Sylow p subgroup-/


 /-Now show if two sylow p subgroups have the same orbit, they are in fact the same subgroup. This is claims 24-31-/


 lemma same_orb_same_grp {G I : Type*} [Group G] {p n : ℕ}
[Fintype G] [Fintype I] [DecidableEq (X' G p n)]
 (V : I → X' G p n) (W : notdivset_orb V → Subgroup G) :
    ∀ (i j : notdivset_orb V), orbit G (V i) = orbit G (V j) → V i = V j := by
      intro x y h
      --ext g
      have h00 : W y = (V y).val := by
        apply Wi_is_Vi V W
      have h₀ : orbit G (V x) = orbit G (V y) → (V x) ∈ orbit G (V y) := by
        intro z
        apply MulAction.orbit_eq_iff.mp z
      have h₁ : (V x) ∈ orbit G (V y) → ∃ (g : G), g • (V y) = (V x) := by
        intro z
        apply MulAction.mem_orbit_iff.mp z
      have h₂ : (W x) = (V x).val := by
        apply Wi_is_Vi V W
      have h₃ : (1 : G) ∈ (V x).val := by
        rw [← h₂]
        exact one_mem (W x)
      have h₄ : ∃ (g : G), g • (V y) = (V x) := by
        apply h₁
        apply h₀
        apply h
      obtain ⟨g, hg⟩ := h₄
      have h₅ : (g • (V y)).val = (V x).val := by
        exact congrArg Subtype.val hg
      have h₆ : (1 : G) ∈ (g • (V y)).val := by
        rw [h₅]
        exact h₃
      have h₇ : g⁻¹ • (1 : G) ∈ (V y).val := by
        exact Set.mem_smul_set_iff_inv_smul_mem.mp h₆
      have h₈ : g⁻¹ • (1 : G) = g⁻¹ * (1 : G) := by
        exact rfl
      have h₉ : g⁻¹ * (1 : G) = g⁻¹ := by
        exact MulOneClass.mul_one g⁻¹
      have h10 : g⁻¹ ∈ (V y).val := by
        rw [← h₉]
        exact h₇
      have h11 : g ∈ (V y).val := by
        rw [ ← h00]
        apply inv_mem_iff.mp
        rw [← h00] at h10
        convert h10
      have h12 : g ∈ W y := by
        rw [← h00] at h11
        apply h11
      have h13 : g • (V y) = V y := by
        ext f
        constructor
        · intro q
          have h14 : f ∈ (g • (V y)).val → g⁻¹ * f ∈ (V y).val := by
            apply (mem_leftCoset_iff g).mp
          have h14_1 : g⁻¹ * f ∈ (V y).val → g⁻¹ * f ∈ W y := by
            rw [← h00]
            exact fun a ↦ a
          have h14_2 : g⁻¹ * f ∈ W y → f ∈ W y := by
            have h14_2a : g⁻¹ ∈ W y := by
              rw [← h00] at h11
              exact (Subgroup.inv_mem_iff (W y)).mpr h11
            apply (mul_mem_cancel_left h14_2a).mp
          have h14_3 : f ∈ W y → f ∈ (V y).val := by
            rw [← h00]
            exact fun a ↦ a
          apply h14_3
          apply h14_2
          apply h14_1
          apply h14
          apply q
        · intro q
          have h15 : f ∈ (V y).val → f ∈ W y := by
            rw [← h00]
            exact fun a ↦ a
          have h15_1 : f ∈ W y → g⁻¹ * f ∈ W y := by
            have h15_1a : g⁻¹ ∈ W y := by
              rw [← h00] at h11
              exact (Subgroup.inv_mem_iff (W y)).mpr h11
            apply (mul_mem_cancel_left h15_1a).mpr
          have h15_2 : g⁻¹ * f ∈ W y → g⁻¹ * f ∈ (V y).val := by
            rw [← h00]
            exact fun a ↦ a
          have h15_3 : g⁻¹ * f ∈ (V y).val → f ∈ (g • (V y)).val := by
            apply (mem_leftCoset_iff g).mpr
          apply h15_3
          apply h15_2
          apply h15_1
          apply h15
          apply q
      rw [hg] at h13
      exact h13


/-So we have that a sylow P subgroup is Vi for some i ∈ notdivset_orb V,
if two sylow P subgroups have the same orbit under left mult by G then they
are the same subgroup. Define a function f from notdivset that takes an index to its corresponding subgroup-/


/- This is where I tried to work around defining the function from {Orbit G Si ∣ p ∤ |Orbit G Si|} to Si by instead 
defining a function from the notdivset, i.e. the set of all indices whose corresponding orbits are not divisible
by p. The flaw is that there is no uniqueness; in the proof, we rely on the fact the Si have distinct orbits, but the 
function defined below could have Orbit(Vi) = (Orbit Vj). This also means the function is not a bijection, as we need 
to'quotient' out by orbits that are equal. And the bijectivity is the very thing we need.-/

def select_orb {G I : Type*} [Group G] {p n : ℕ} [Fintype G] [Fintype I]
 [DecidableEq (X' G p n)] (V : I → X' G p n) (j : notdivset_orb V) : X' G p n := orb_choice V j


/-need to show this function is well defined. If orbit Vi = orbit Vj then Vi = Vj-/
 lemma select_welldefined {G I : Type*} [Group G] {p n : ℕ}
 [Fintype G] [Fintype I] [DecidableEq (X' G p n)] (V : I → X' G p n)
  {U : I → Set ↑(X' G p n)} (huv : ∀ (i : I), U i = orbit G (V i))
  (W : notdivset_orb V → Subgroup G) :
  ∀ (i j : notdivset_orb V), i = j → select_orb V i = select_orb V j := by
  have h00 : ∀ (i j : notdivset_orb V), orbit G (V i) = orbit G (V j) → V i = V j := by
    apply same_orb_same_grp V W
  have h₀ : ∀ (i j : notdivset_orb V), i = j → U i = U j := by
    exact fun i j a ↦ congrArg U (congrArg Subtype.val a)
  have h₁ : ∀ (i : notdivset_orb V), U i = orbit G (V i) := by
    exact fun i ↦ huv ↑i
  have h₂ : ∀ (i j : notdivset_orb V), U i = U j → orbit G (V i) = orbit G (V j) := by
    intro x y
    rw [← h₁, ← h₁]
    exact fun a ↦ a
  have h₃ : ∀ (i j : notdivset_orb V), orbit G (V i ) = orbit G (V j) → V i = V j := by
    exact h00
  have h₄ : ∀ (i : notdivset_orb V), V i = orb_choice V i := by
    exact fun i ↦ h00 i i (h₂ i i (h₀ i i rfl))
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

/-The final statement of claim 2 is written in the conclusion as step 37-/

 -----------------------------------------------------------------------------------------------------------------------------------
 /-BIJECTIVITY STATEMENTS: IF THERE'S A BIJECTION BETWEEN FINITE SETS THEN THE SETS HAVE THE SAME CARDINALITY-/
 -----------------------------------------------------------------------------------------------------------------------------------


/-in order to show |notdivset_orb V| = |Syl p G|, we show there is a bijection between them, which will hopefully be whatever version of select we write tomorrow using the Si Reece defines. First define injection, surjection and bijection -/
def inj (X Y : Type*) (f : X → Y) := ∀ (x : X) , ∀ (y : X) , f x = f y → x = y
def surj (X Y : Type*) (f : X → Y) := ∀ (y : Y) , ∃ (x : X) , f x = y
def bij (X Y : Type*) (f : X → Y) := inj X Y f  ∧ surj X Y f


/-Now prove if there's a bijection between two finite sets then they have the same cardinality-/


/-First show if there's an injection from a finite set G to a finite set H then |G| ≤ |H|-/
lemma inj_card {G H : Type*} [Fintype G] [Fintype H]
(f : G → H) (hinj : inj G H f) : Fintype.card G ≤ Fintype.card H := by
  exact Fintype.card_le_of_injective f hinj




/-Now show if there's a surjection from a finite set G to finite set H then |H| ≤ |G|-/
lemma surj_card {G H : Type*} [Fintype G] [Fintype H]
 (f : G → H) (hsurj : surj G H f) : Fintype.card H ≤ Fintype.card G := by
  exact Fintype.card_le_of_surjective f hsurj


/-If there's a bijection between finite sets then these sets have the same cardinality-/
theorem bij_card {G H : Type*} [Fintype G] [Fintype H]
 : (∃ (f : G → H), bij G H f) → Fintype.card G = Fintype.card H := by
  intro hx
  obtain ⟨f,hf⟩ := hx
  cases hf with
  | intro left right
  apply le_antisymm
  · apply inj_card f left
  · apply surj_card f right


-------------------------------------------------------------------------------------------------------------------------
/-CONCLUSION-/
--------------------------------------------------------------------------------------------------------------------------


 /-we aim to show |notdivset_orb V| = |Syl p G|-/ 


/-Have p is prime-/
variable {p n : ℕ} [Fact p.Prime]


-- Since we defined the set X in different way in the number theory section to the claim 1 section,
-- we need to link them first
lemma card_X_eq_card_Xsubsets {G : Type*} [Group G] [Fintype G] {p n : ℕ} :
    Nat.card (X' G p n) = (Xsubsets G p n).card := by
  -- X G p n = {S : Set G | Nat.card S = p ^ n}
  -- Xsubsets G p n = Finset.powersetCard (p^n) Finset.univ
  sorry


lemma nat_cast_zmod_eq_iff_modeq {a b p : ℕ} [Fact p.Prime] :
    (a : ZMod p) = (b : ZMod p) ↔ a ≡ b [MOD p] := by
  rw [ZMod.natCast_eq_natCast_iff]


-- prove the conclusion 34：|X| = m (mod p)
theorem card_X_modeq_sum {G : Type*} [Group G] [Fintype G]
    {p n m : ℕ} [hp : Fact p.Prime]
    (hG : Fintype.card G = p ^ n * m)
    (hm : Nat.Coprime m p) :
    Nat.card (X' G p n) = (m : ZMod p) := by


  letI : DecidableEq (X' G p n) := Classical.decEq _


  have h1 : Nat.card (X' G p n) = (Xsubsets G p n).card :=
    card_X_eq_card_Xsubsets
  have h2 : (Xsubsets G p n).card = (p ^ n * m).choose (p ^ n) :=
    Xsubsets_card G p n m hG


  have h3 : ((p ^ n * m).choose (p ^ n) : ZMod p) = (m : ZMod p) :=
    binomial_prime_pow_mul hp.out


  rw [h1, h2]


  exact h3


/--step 35-/
/-Size of X is sum of size of orbits-/
theorem X_sum_orbits
  [Fintype (X' G p n)]
  [Fintype (OrbitIndex G (X' G p n))] :
  Fintype.card (X' G p n)
    =
  ∑ᶠ i : OrbitIndex G (X' G p n),
      Fintype.card (orbit G (S_i (G := G) (p := p) (n := n) i)) := by
  classical


  -- Apply card_union_disj to OrbitFamily
  have hV : ∀ i : OrbitIndex G (X' G p n),
      (OrbitFamily (G := G) (X' := X' G p n) i).Finite :=
    fun i => OrbitFamily_finite (G := G) (p := p) (n := n) i


  have hdisj :
      Pairwise (fun i j =>
        Disjoint (OrbitFamily (G := G) (X' := X' G p n) i)
                 (OrbitFamily (G := G) (X' := X' G p n) j)) :=
    OrbitFamily_pairwise_disjoint (G := G) (X' := X' G p n)


  have hncard_union :
      (⋃ i : OrbitIndex G (X' G p n),
          OrbitFamily (G := G) (X' := X' G p n) i).ncard
        =
      ∑ᶠ i : OrbitIndex G (X' G p n),
        (OrbitFamily (G := G) (X' := X' G p n) i).ncard :=
    card_union_disj (hV := hV) hdisj


  -- Rewrite the LHS union to univ
  have hncard_univ :
      (Set.univ : Set (X' G p n)).ncard
        =
      ∑ᶠ i : OrbitIndex G (X' G p n),
        (OrbitFamily (G := G) (X' := X' G p n) i).ncard := by
    -- substitute iUnion = univ
    simpa [iUnion_OrbitFamily_eq_univ (G := G) (p := p) (n := n)] using hncard_union


  -- Replace each OrbitFamily by orbit of S_i, then convert ncard(univ) to card
  have hncard_terms :
      (∑ᶠ i : OrbitIndex G (X' G p n),
          (OrbitFamily (G := G) (X' := X' G p n) i).ncard)
        =
      (∑ᶠ i : OrbitIndex G (X' G p n),
          (orbit G (S_i (G := G) (p := p) (n := n) i)).ncard) := by
    refine finsum_congr ?_
    intro i
    simpa [OrbitFamily_eq_orbit_Si (G := G) (p := p) (n := n) i]


  -- Final calculation:
  -- card X = ncard univ = finsum ncard orbit = finsum card orbit
  calc
    Fintype.card (X' G p n)
        = (Set.univ : Set (X' G p n)).ncard := by
            simpa using (Set.ncard_univ (α := X' G p n)).symm
    _   = ∑ᶠ i : OrbitIndex G (X' G p n),
            (OrbitFamily (G := G) (X' := X' G p n) i).ncard := hncard_univ
    _   = ∑ᶠ i : OrbitIndex G (X' G p n),
            (orbit G (S_i (G := G) (p := p) (n := n) i)).ncard := by
            simpa [hncard_terms]
    _   = ∑ᶠ i : OrbitIndex G (X' G p n),
          Fintype.card (orbit G (S_i (G := G) (p := p) (n := n) i)) := by
      classical
      refine finsum_congr ?_
      intro i


      -- Use existing orbit fintype instance
      letI : Fintype (↑(orbit G (S_i (G := G) (p := p) (n := n) i))) :=
        orbit_fintype (G := G) (X' := X' G p n) (S_i (G := G) (p := p) (n := n) i)


      -- We have finiteness of the orbits
      have hs :
          (orbit G (S_i (G := G) (p := p) (n := n) i)).Finite :=
        orbit_finite (G := G) (X' := X' G p n)
          (S_i (G := G) (p := p) (n := n) i)


      -- This comes down to a ncard vs fintype.card issue that cannot be easily solved, but ran out of time to sort it
      have :
          (orbit G (S_i (G := G) (p := p) (n := n) i)).ncard
            =
          Fintype.card (↑(orbit G (S_i (G := G) (p := p) (n := n) i))) := by
        sorry
      exact this


--need to split this sum into a sum over orbits that are divisible by p, and ones that aren't


/-Need notdivset_orb V to be a fintype in order to use fintype.card-/


/-define the set of indices whose corresponding sets have orbits that are divisible by p-/
def divset_Si [Fintype (X' G p n)] [Fintype (OrbitIndex G (X' G p n))] : Set (OrbitIndex G (X' G p n)) :=
{(i : OrbitIndex G (X' G p n)) | p ∣ Fintype.card (orbit G (S_i (G := G) (p := p) (n := n) i))}


def notdivset_Si [Fintype (X' G p n)] [Fintype (OrbitIndex G (X' G p n))] : Set (OrbitIndex G (X' G p n)) :=
{(i : OrbitIndex G (X' G p n)) | ¬ (p ∣ Fintype.card (orbit G (S_i (G := G) (p := p) (n := n) i)))}


/-Show every i in I is either in notdivset_Si or divset_Si-/
 lemma div_paritions_I [Fintype (X' G p n)] [Fintype (OrbitIndex G (X' G p n))] : 
 ∀ (i : OrbitIndex G (X' G p n)), i ∈ (notdivset_Si) ∪ (divset_Si) := by
  intro k
  unfold notdivset_Si
  unfold divset_Si
  sorry

 /-Show the sum can be split into a sum over notdivset and divset-/
theorem X_sum_by_div
  [Fintype (X' G p n)]
  [Fintype (OrbitIndex G (X' G p n))] :
  Fintype.card (X' G p n)
    =
  (∑ᶠ (i : (notdivset_Si : Set (OrbitIndex G ↑(X' G p n)))),
      Fintype.card (orbit G (S_i (G := G) (p := p) (n := n) i))) +   (∑ᶠ (i : (divset_Si : Set (OrbitIndex G ↑(X' G p n)))),
      Fintype.card (orbit G (S_i (G := G) (p := p) (n := n) i))):= by
        sorry

/-step 35: |X| ≡ ∑ (orbits whose size is not divisible by p) mod p-/
lemma X_sum_mod_p [Fintype (X' G p n)]
  [Fintype (OrbitIndex G (X' G p n))] :
  (Fintype.card (X' G p n) : ZMod p)
    =
  (∑ᶠ (i : (notdivset_Si : Set (OrbitIndex G ↑(X' G p n)))),
      Fintype.card (orbit G (S_i (G := G) (p := p) (n := n) i))) := by
  have h := X_sum_by_div (G := G) (p := p) (n := n)
  conv_lhs => rw [h]
  push_cast

  have hzero : ∀ (i : (divset_Si : Set (OrbitIndex G ↑(X' G p n)))),
      (Fintype.card (orbit G (S_i (G := G) (p := p) (n := n) i)) : ZMod p) = 0 := by
    intro i
    have hi : i.val ∈ divset_Si := i.property
    unfold divset_Si at hi
    simp only [Set.mem_setOf_eq] at hi

    obtain ⟨k, hk⟩ := hi
    rw [hk]
    rw [Nat.cast_mul]

    norm_num

  have hdiv : (∑ᶠ (i : (divset_Si : Set (OrbitIndex G ↑(X' G p n)))),
      (Fintype.card (orbit G (S_i (G := G) (p := p) (n := n) i)) : ZMod p)) = 0 := by
    simp only [hzero, finsum_zero]
  rw [hdiv, add_zero]

open MulAction
-- We want to prove conclusion 36 with claim 1
-- However, we need to transform claim one to single set form first
-- It is almost same as the proof of claim one except that we delete the index i
theorem claim_1_seteq_single {G : Type*} [Group G] {p n : ℕ}
    (S : X' G p n)
    (H : Subgroup G)
    (hH : (H : Set G) = S.val) :
    (stabilizer G S : Set G) = S.val := by
  ext g
  constructor
  · intro hg
    have h1_in_S : (1 : G) ∈ S.val := by
      rw [← hH]
      exact OneMemClass.one_mem H
    have : S.val = (g • S).val := by rw [hg]
    rw [this]
    exact ⟨1, h1_in_S, mul_one g⟩
  · intro hg_in_S
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, rfl⟩ := hx
      rw [← hH] at hg_in_S hs ⊢
      exact mul_mem hg_in_S hs
    · intro hx
      use g⁻¹ * x
      constructor
      · rw [← hH] at hg_in_S hx ⊢
        exact mul_mem (inv_mem hg_in_S) hx
      · exact mul_inv_cancel_left g x


-- Proof of conclusion 36
theorem orbit_size_eq {G : Type*} [Group G] [Fintype G] {p n : ℕ}
    (S : X' G p n)
    (H : Subgroup G)
    (hH : (H : Set G) = S.val) :
    Fintype.card (orbit G S) * p ^ n = Fintype.card G := by


  letI : DecidableEq (X' G p n) := Classical.decEq _


  have h1 := orbit_stabilizer_theorem G (X' G p n) S
  -- h1 : Fintype.card G = Fintype.card (orbit G S) * Fintype.card (stabilizer G S)


  -- Prove Fintype.card (stabilizer G S) = p ^ n
  have h_stab : Fintype.card (stabilizer G S) = p ^ n := by
    rw [← Nat.card_eq_fintype_card]
    have h2 : stabilizer G S = H := by
      apply SetLike.coe_injective
      rw [claim_1_seteq_single S H hH, hH]
    rw [h2]
    exact H_card_eq_pow S H hH


  -- combine the result
  rw [h_stab] at h1
  exact h1.symm

/-step 37: the final statement of claim2 we were aiming for but sadly didn't reach-/
lemma syl_bij_notdivset  [Fintype (X' G p n)]
  [Fintype (OrbitIndex G (X' G p n))] :
  Nat.card (notdivset_Si : Set (OrbitIndex G (X' G p n))) = Nat.card (Syl_p G p) := by sorry

--claim 38
lemma sum_substituted_modp [Fintype (X' G p n)]
  [Fintype (OrbitIndex G (X' G p n))]
  {m : ℕ} (hp : p.Prime)
  (hG : Fintype.card G = p ^ n * m) :
  (Fintype.card (X' G p n) : ZMod p)
    = (Fintype.card G / p^n : ℕ) * Nat.card (notdivset_Si : Set (OrbitIndex G (X' G p n))) := by
  
  have hdiv : Fintype.card G / p^n = m := by
    rw [hG]; exact Nat.mul_div_cancel_left m (pow_pos hp.pos n)
  
  rw [X_sum_mod_p]
  
  have hsize : ∀ (i : (notdivset_Si : Set (OrbitIndex G (X' G p n)))),
      Fintype.card (orbit G (S_i (G := G) (p := p) (n := n) i.val)) = (Fintype.card G) / p^n := by
    intro i
    have ⟨H, hH⟩ : ∃ H : Subgroup G, (H : Set G) = (S_i i.val).val := sorry
    exact orbit_size_eq (S_i i.val) hp H hH
  
  have hsum_eq : (∑ᶠ (i : (notdivset_Si : Set (OrbitIndex G ↑(X' G p n)))),
      Fintype.card (orbit G (S_i (G := G) (p := p) (n := n) i))) = 
    (∑ᶠ (i : (notdivset_Si : Set (OrbitIndex G ↑(X' G p n)))),
      (Fintype.card G / p^n : ℕ)) := by
    congr 1; ext i; exact hsize i
  
  rw [hsum_eq]
  
  have hsum_nat : (∑ᶠ (i : (notdivset_Si : Set (OrbitIndex G ↑(X' G p n)))),
        (Fintype.card G / p^n : ℕ)) = 
      Nat.card (notdivset_Si : Set (OrbitIndex G (X' G p n))) * (Fintype.card G / p^n) := by
    classical
    rw [finsum_eq_sum_of_fintype]
    rw [Finset.sum_const]
    rw [nsmul_eq_mul, Finset.card_univ]
    congr 1
    exact Nat.card_eq_fintype_card.symm
  
  rw [hsum_nat, Nat.cast_mul, hdiv, mul_comm]


/-For claim 39, need to premultiply by inverse of m mod p. First show this inverse exists-/
  -- if m and p are coprime, then m has has an inverse mod p
theorem zmodp_coprime_inverse (m p : ℕ) (b : ZMod p) (hp : p.Prime) (h : Nat.Coprime m p) :
    (m = m * b) → (1 = b) := by


  -- factors p prime into zmod p so we can use the fact
  -- that it's a multiplicative group with a zero term
  haveI : Fact p.Prime := ⟨hp⟩


  intro modeq
  let m_inv := (m : ZMod p)⁻¹


  -- we require m != 0 for it to have an inverse
  have h_m_neq_zero : (m ≠ (0 : ZMod p)) := by
    exact m_coprime_nonzero_mod_p m p hp h


  -- multiply both sides by m^-1
  have inv_eq : m_inv * (m : ZMod p) = m_inv * ((m : ZMod p) * b) := by
    exact congrArg (HMul.hMul m_inv) modeq


  rw [← mul_assoc] at inv_eq


  -- zmod p is a group with zero (as p is prime), so nonzero elements have an inverse
  have h_inv : m_inv * (m : ZMod p) = 1 := by
    exact inv_mul_cancel₀ h_m_neq_zero


  rw [h_inv, one_mul] at inv_eq
  exact inv_eq


/-claim 39 - the size of the set of sylow p subgroups is congruent to 1 mod p-/
lemma syl_congr_1 {G : Type*} [Group G] [Fintype G]
    {p n m : ℕ} [hp : Fact p.Prime] [Fintype (X' G p n)]
  [Fintype (OrbitIndex G (X' G p n))] (hG : Fintype.card G = p ^ n * m)
    (hm : Nat.Coprime m p)
  : (Fintype.card (X' G p n) : ZMod p)
    = Nat.card (notdivset_Si : Set (OrbitIndex G (X' G p n))) * ((Fintype.card G) / p^n) := by
  rw [sum_substituted_modp]
  ring
