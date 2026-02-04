--skeleton 9 & 10
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

/-
---------------------------------
IMPORTANT IMPORTANT IMPORTANT
---------------------------------
MAKE SURE ORBITS ARE OF THE RIGHT TYPE TO USE MY STUFF; NEED
TO BE ABLE TO HAVE V_i = Orb(S_i)
THERE SEEM TO BE PROBELMS UNIFYING ORBIT STAB ETC AND MY STUFF
WITH THE NEW INSTANCE X G n p THING, MAKING CLAIM 2 TRICKY

-/
open MulAction

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


def X (G : Type*) [Group G] (p n : ℕ) : Set (Set G):=
  {S : Set G | Nat.card S = p ^ n}

-- G is a finite group
variable {G : Type*} [Group G] [Fintype G] (p n : ℕ)

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


-- if |H| = p^n，then H is p-group
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

-- unsure how to get the necessary assumptions from the definition of X G p n

/-
def set_of_pnotdiv_orbits [Group G] {p n : ℕ} [Fintype G] [MulAction G (X G p n)]
 [DecidableEq (X G p n)] : Set (Set ↑(X G p n)) := {orbit G P |  P : X G p n }

/- (V : I → {orbit G P |  P : X G p n })
(hV : ∀ (i : I), Fintype (V i))
 (S : (notdivset p hV) → X G p n)
    (H : (notdivset p hV) → Subgroup G)
    (hH : ∀ i, (H i : Set G) = (S i).val)-/

--(V : I → {orbit G P |  P : X G p n })
--{V : {orbit G P | P : X G p n} → X G p n}
-- {V : ↑(X G p n) → X G p n}
def select {G : Type*} [Group G] {p n : ℕ} [Fintype G] [MulAction G (X G p n)]
 [DecidableEq (X G p n)] {P : X G p n} (hj: orbit G P ∈ set_of_orbits): X G p n := P

-/


variable {α : Type*} (I : Finset α) (p : ℕ)
--says p divides the order of each set in the sum indezed over range n

def icard {U : Type u} {I : Type v} [Fintype I]
{V : I → Set U} (i : I) (hV : ∀ (i : I), Fintype (V i))
: ℕ := Fintype.card (V i)

/- check definition of icard makes sense
example {U : Type u} {I : Type v} [Fintype I]
(V : I → Set U) (hV : ∀ (i : I), Fintype (V i)) (i : I)
 : icard i hV = Fintype.card (V i) := by
  unfold icard
  trivial
-/

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

--define the set of all i in I such that p ∤ |Vᵢ|
def notdivset {U : Type u} {I : Type v} [Fintype I] (p : ℕ)
{V : I → Set U} (hV : ∀ (i : I), Fintype (V i))
 := {k : I | ¬ (p ∣ Fintype.card (V k))}

/-
noncomputable instance notdivset_fintype {U : Type u} {I : Type v} [Fintype I] (p : ℕ)
{V : I → Set U} (hV : ∀ (i : I), Fintype (V i)) : Fintype (notdivset p hV) :=
  (Set I).fintype
  -/

--gives the subset J of the index I of the sum so that we can split the sum
-- into a sum over J, where p ∤ |Vⱼ| and a sum over I \ J where p | |Vᵢ|
-- here we show that this J is non-empty

lemma notdivset_nonempty {U : Type u} {I : Type v} [Fintype I] (p : ℕ)
{V : I → Set U} (hV : ∀ (i : I), Fintype (V i))
(hdiv : ¬ (p ∣ ∑ᶠ (i : I), Fintype.card (V i))) :
 ∃ (k : I), k ∈ notdivset p hV  := by
  have h₀ : ∃ (k : I), ¬ (p ∣ Fintype.card (V k)) := by
    apply not_div_sum
    exact hdiv
  exact h₀

lemma not_div_then_in_notdivset {U : Type u} {I : Type v} [Fintype I] (p : ℕ)
{V : I → Set U} (hV : ∀ (i : I), Fintype (V i)) :
 ∀ (i : I), ¬ (p ∣ Fintype.card (V i)) → i ∈ notdivset p hV := by
 unfold notdivset
 exact fun i a ↦ a

/-
lemma notdiv_index_subset {U : Type u} {I : Type v} [Fintype I] (p : ℕ)
{V : I → Set U} (hV : ∀ (i : I), Fintype (V i))
(hdiv : ¬ (p ∣ ∑ᶠ (i : I), Fintype.card (V i))) :
 ∃ (J : Finset I), Nonempty J → ∀ (j : J), ¬ (p ∣ Fintype.card (V j)) := by
  have h₀ : ∃ (k : I), ¬ (p ∣ Fintype.card (V k)) := by
    apply not_div_sum
    exact hdiv
  have h₁ : Nonempty (notdivset p hV) := by
    unfold notdivset
    exact nonempty_subtype.mpr h₀
  have h₂ : Fintype (notdivset p hV) := by
    exact ofFinite ↑(notdivset p hV)
  use (notdivset p hV).toFinset
  simp
  exact fun x h a b ↦ b
-/

--this is needed for claim 2 (24): if i ∈ I, i ∉ J then p ∣ |Vi|.
/-
lemma rearrange_10 {U : Type u} {I : Type v} [Fintype I] (p : ℕ)
{V : I → Set U} (hV : ∀ (i : I), Fintype (V i)) :
∀ (i : I), i ∉ {j : I | ¬ (p ∣ Fintype.card (V j))}
  → i ∈ {j : I | p ∣ Fintype.card (V j)} := by
  intro x hx
  contrapose hx
  refine not_not_intro ?_
  exact hx
-/

def select {G I : Type*} [Group G] {p n : ℕ} [Fintype G] [Fintype I] [MulAction G (X G p n)]
 [DecidableEq (X G p n)] {V : I → X G p n} (hV : ∀ (i : I), Fintype (V i))
 (S : notdivset p hV → X G p n)
 {U : I → Set ↑(X G p n)}
 (huv : ∀ (i : I), U i = orbit G (V i))
  (j : notdivset p hV) : X G p n :=  S j

lemma select_welldef1 {G I : Type*} [Group G] {p n : ℕ}
 [Fintype G] [Fintype I] [MulAction G (X G p n)] [DecidableEq (X G p n)] {V : I → X G p n}
 (hV : ∀ (i : I), Fintype (V i))
  (S : notdivset p hV → X G p n) (hVS : ∀ (i : notdivset p hV), V i = S i)
 {U : I → Set ↑(X G p n)} (huv : ∀ (i : I), U i = orbit G (V i))
  (hdistinct : ∀ (i j : notdivset p hV), orbit G (V i) = orbit G (V j) → V i = V j) :
  ∀ (i j : notdivset p hV), i = j → S i = S j := by
  have h₀ : ∀ (i j : notdivset p hV), i = j → U i = U j := by
    exact fun i j a ↦ congrArg U (congrArg Subtype.val a)
  have h₁ : ∀ (i : notdivset p hV), U i = orbit G (V i) := by
    exact fun i ↦ huv ↑i
  have h₂ : ∀ (i j : notdivset p hV), U i = U j → orbit G (V i) = orbit G (V j) := by
    intro x y
    rw [← h₁, ← h₁]
    exact fun a ↦ a
  have h₃ : ∀ (i j : notdivset p hV), orbit G (V i ) = orbit G (V j) → V i = V j := by
    exact hdistinct
  have h₄ : ∀ (i : notdivset p hV), V i = S i := by
    exact fun i ↦ hVS i
  have h₅ : ∀ (i j : notdivset p hV), V i = V j → S i = S j := by
    intro x y
    rw [← h₄, ← h₄]
    exact fun a ↦ a
  intro x y eq
  apply h₅
  apply h₃
  apply h₂
  apply h₀
  exact eq

theorem claim_1_2 {G I : Type*} [Group G] {p n : ℕ} [Fintype I] {V : I → X G p n}
 (hV : ∀ (i : I), Fintype (V i))
    (S : notdivset p hV → X G p n)
    (H : notdivset p hV → Subgroup G)
    (hH : ∀ i, (H i : Set G) = (S i).val)
    (i : notdivset p hV) :
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



theorem claim_1_2_subgroup {G I : Type*} [Group G] {p n : ℕ} [Fintype I] {V : I → X G p n}
 (hV : ∀ (i : I), Fintype (V i))
    (S : notdivset p hV → X G p n)
    (H : notdivset p hV → Subgroup G)
    (hH : ∀ i, (H i : Set G) = (S i).val)
    (i : notdivset p hV) :
    H i = stabilizer G (S i) := by
  have h := claim_1_2 hV S H hH i
  apply SetLike.coe_injective
  rw [hH i, ← h]

/-
lemma select_welldef2 {G I : Type*} [Group G] {p n : ℕ}
 [Fintype G] [Fintype I] {V : I → X G p n} [DecidableEq (X G p n)]
 (hV : ∀ (i : I), Fintype (V i)) (S : notdivset p hV → X G p n)
 (hS : ∀ (i : notdivset p hV), Fintype (S i))
 (hss : ∀ (i : notdivset p hV), Fintype (stabilizer G (S i)))
 (H : notdivset p hV → Subgroup G) (hVS : ∀ (i : notdivset p hV), V i = S i)
  (hH : ∀ i, (H i : Set G) = (S i).val)
 {U : I → Set ↑(X G p n)} (huv : ∀ (i : I), U i = orbit G (V i)) :
  ∀ (i : notdivset p hV), Fintype.card (S i) = p^n := by
    have h₀ : ∀ (i : notdivset p hV), H i = stabilizer G (S i) := by
      intro x
      apply claim_1_2_subgroup hV S H hH x
    have h₁ : ∀ (i : notdivset p hV),
    Fintype.card G = Fintype.card (orbit G (S i)) * Fintype.card (stabilizer G (S i)) := by
      intro x
      convert orbit_stabilizer_theorem G (X G p n) (S x)
-/

lemma select_inj {G I : Type*} [Group G] {p n : ℕ}
 [Fintype G] [Fintype I] {V : I → X G p n} [DecidableEq (X G p n)]
 (hV : ∀ (i : I), Fintype (V i)) (S : notdivset p hV → X G p n) :
  ∀ (i j : notdivset p hV), S i = S j → orbit G (S i) = orbit G (S j) := by
    exact fun i j a ↦ congrArg (orbit G) a

lemma claim22 {G I : Type*} [Group G] {p n : ℕ}
 [Fintype G] [Fintype I] {V : I → X G p n} [DecidableEq (X G p n)]
  (P : X G p n) (H : Subgroup G) (hgrp : H = P.val)
 : stabilizer G P = P.val := by
  ext g
  constructor
  ·
    intro hg
    have h1_in_P : (1 : G) ∈ (P).val := by
      rw[← hgrp]
      exact OneMemClass.one_mem H
    have h₀ : P.val = (g • P).val := by
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


lemma claim23 {G : Type*} [Group G] {p n r m : ℕ} [Fintype G] [MulAction G (X G p n)]
 [DecidableEq (X G p n)]
    (P : X G p n)
    (hsame : stabilizer G (P) = (P).val)
    (hS : Fintype (stabilizer G (P)))
    (hP : Fintype P)
    (hm : p.Coprime m)
    (P_order : Fintype.card (P).val = p^n)
    (G_order : Fintype.card G = m * p^n)
    (hPrime : Nat.Prime p) :
    ∀ (P : X G p n), ¬ (p ∣ Fintype.card (orbit G P)) := by
    intro W
    have hsorry1 : Fintype W := by sorry
    have hsorry2 : stabilizer G W = W.val := by sorry
    have hsorry3 : Fintype.card W.val = p^n := by sorry
    have h₀ : Fintype.card G = Fintype.card (orbit G W) * Fintype.card (stabilizer G W) := by
      convert orbit_stabilizer_theorem G (X G p n) W
    have h₁ : Fintype.card (orbit G W) = Fintype.card G / Fintype.card (stabilizer G W) := by
      refine Nat.eq_div_of_mul_eq_right ?_ ?_
      · exact Fintype.card_ne_zero
      apply Eq.symm
      rw [mul_comm]
      apply h₀
    have h₂ : Fintype.card (stabilizer G W) = Fintype.card W := by
      apply Fintype.card_congr'
      convert hsorry2
      exact (iff_true_right hsorry2).mpr (congrArg Subtype hsorry2)
    have h₃ : Fintype.card (orbit G W) = m * p^n / p^n:= by
      rw [G_order] at h₁
      rw [h₂] at h₁
      rw [hsorry3] at h₁
      apply h₁
    have h₄ : m = m * p^n / p^n := by
     refine Nat.eq_div_of_mul_eq_right ?_ ?_
     ·
      refine pow_ne_zero n ?_
      exact Nat.Prime.ne_zero hPrime
     ·
      exact Nat.mul_comm (p ^ n) m
    have h₅ : Fintype.card (orbit G W) = m := by
      rw [h₄]
      exact h₃
    have h₆ : p ∣ m ↔ ¬ p.Coprime m:= by
      apply Nat.Prime.dvd_iff_not_coprime hPrime
    have h₇ : ¬ p ∣ m ↔ p.Coprime m := by
      exact Decidable.not_iff_comm.mp (id (Iff.symm h₆))
    have h₈ : ¬ p ∣ m := by
      rw [h₇]
      exact hm
    have h₉ : ¬ p ∣ Fintype.card (orbit G W) := by
      rw [h₅]
      exact h₈
    exact h₉









/-
def notdivset {U : Type u} {I : Type v} [Fintype I] (p : ℕ)
{V : I → Set U} (hV : ∀ (i : I), Fintype (V i))
 := {k : I | ¬ (p ∣ Fintype.card (V k))}

lemma not_div_then_in_notdivset {U : Type u} {I : Type v} [Fintype I] (p : ℕ)
{V : I → Set U} (hV : ∀ (i : I), Fintype (V i)) :
 ∀ (i : I), ¬ (p ∣ Fintype.card (V i)) → i ∈ notdivset p hV := by
 unfold notdivset
 exact fun i a ↦ a-/


lemma claim24 {G : Type*} [Group G] {p n r : ℕ} [Fintype G] [DecidableEq (X G p n)]
    (P : X G p n)
    (S : Fin r → X G p n)
    (i : Fin r)
    (hsame : (stabilizer G (P) : Set G) = (P).val)
    (hS : ∀ (i : Fin r), Fintype (S i)) :
    --(hsylp : ∀ (i : Fin r), Nat.card (S i) = p ^ n) :
    ∃ i, orbit G P = orbit G (S i) := by
    sorry
