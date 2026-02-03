import SylowTheromsProject.OribitStabiliser
import SylowTheromsProject.Claim1
import SylowTheromsProject.NumberTheory

open MulAction

-- Conclusion part:

-- Since we defined the set X in different way
-- we need to link them first
lemma card_X_eq_card_Xsubsets {G : Type*} [Group G] [Fintype G] {p n : ℕ} :
    Nat.card (X G p n) = (Xsubsets G p n).card := by
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
    Nat.card (X G p n) = (m : ZMod p) := by

  letI : DecidableEq (X G p n) := Classical.decEq _

  have h1 : Nat.card (X G p n) = (Xsubsets G p n).card :=
    card_X_eq_card_Xsubsets
  have h2 : (Xsubsets G p n).card = (p ^ n * m).choose (p ^ n) :=
    Xsubsets_card G p n m hG

  have h3 : ((p ^ n * m).choose (p ^ n) : ZMod p) = (m : ZMod p) :=
    binomial_prime_pow_mul hp.out

  rw [h1, h2]
  
  exact h3

-- We want to prove conclusion 36 with claim 1
-- However, we need to transform claim one to single set form first
-- It is almost same as the proof of claim one except that we delect the index i
theorem claim_1_seteq_single {G : Type*} [Group G] {p n : ℕ}
    (S : X G p n)
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
    (S : X G p n)
    (H : Subgroup G)
    (hH : (H : Set G) = S.val) :
    Fintype.card (orbit G S) * p ^ n = Fintype.card G := by

  letI : DecidableEq (X G p n) := Classical.decEq _

  have h1 := orbit_stabilizer_theorem G (X G p n) S
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
