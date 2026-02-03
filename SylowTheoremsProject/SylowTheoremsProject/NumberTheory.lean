-- def hello := "world"

import SylowTheromsProject.Imports

open ZMod

-- rewrite to make follow proof from notes rather than using mathlib?
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

------------------------------------------------------------------------------------

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
