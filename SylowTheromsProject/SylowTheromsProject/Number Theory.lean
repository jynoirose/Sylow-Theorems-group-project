-- def hello := "world"

import Mathlib.GroupTheory.Sylow -- test
import Mathlib.Data.Nat.Prime.Basic  -- test
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic -- reduce these imports later

#check Nat.Prime --test
#check Sylow --test
#eval 2 + 3 --test

open ZMod

-- theorem sylow_1 {p n : ℕ} {G : Type*} [Group G] [Fintype G]
--     (hp : p.Prime)
--     (hpdivG : p ^ n ∣ Nat.card G)
--     (hpdivg2 : ¬(p^(n+1) ∣ Nat.card G)) :
--     ∃ (H : Subgroup G), Nat.card H = p ^ n := by

--   sorry

theorem binomial_prime_mul {p i : ℕ} (hp : p.Prime) (hip : 0 < i ∧ i < p) : p ∣ (p.choose i) := by
  sorry

theorem binomial_prime_pow_mul {p n m : ℕ} (hp : p.Prime) (hmp : m.Coprime p) :
    (Nat.choose (p^n * m) (p^n) : ZMod p) = (m : ZMod p) := by
  sorry

open Polynomial

variable {R : Type*} [Semiring R] {r : R}

-- i should to make this less ugly
-- proof that (1+X)^p=1+X^p mod p
theorem binomial_pow_p_mod_p {p : ℕ} (hp : p.Prime) : (1 + X : (ZMod p)[X]) ^ p = 1 + X ^ p := by
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
  have h_div : p ∣ (Nat.choose p n) := by
    apply binomial_prime_mul hp
    exact ⟨n_pos, n_in_range_p⟩
  have h_zero : (p.choose n : ZMod p) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact h_div
  rw [← Polynomial.C_eq_natCast]
  rw [h_zero]
  simp

theorem binomial_pow_p_n_mod_p {p n : ℕ} {hp : p.Prime} :
    (1 + X : (ZMod p)[X]) ^ (p ^ n) = 1 + X ^ (p ^ n) := by

  have composed_lemma := binomial_pow_p_mod_p hp
  induction n with
  | zero =>
    simp
  | succ d hd =>
    rw [pow_succ, pow_mul]
    apply_fun (fun f => f.comp (X ^ (p ^ d))) at composed_lemma
    simp at composed_lemma
    rw [hd, composed_lemma, pow_mul]

theorem binomial_pow_p_n_m_mod_p {p n m : ℕ} {hp : p.Prime} :
    (1 + X : (ZMod p)[X]) ^ ((p ^ n) * m) = (1 + X ^ (p ^ n)) ^ m := by

  sorry


theorem test {a b m p : ℕ} {hp : p.Prime} {h : a = (b : (ZMod p))} : a^m = (b^m : ZMod p) := by

  exact congrFun (congrArg HPow.hPow h) m
