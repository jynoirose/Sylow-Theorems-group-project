--thus V is in fact from notdivset, i.e. notdivset = I
lemma claim24_pt1 {G I : Type*} [Group G] {p n m : ℕ}
 [Fintype G] [Fintype I] [DecidableEq (X G p n)]
 (V : I → X G p n) (i : I)
    (hS : Fintype (stabilizer G (V i)))
    (hP : Fintype (V i))
    (hm : p.Coprime m)
    (H : Subgroup G) (hgrp : H = (V i).val)
    (P_order : Fintype.card (V i).val = p^n)
    (G_order : Fintype.card G = m * p^n)
    (hPrime : Nat.Prime p) : i ∈ notdivset_orb V := by
    have h₀ : ¬ (p ∣ Fintype.card (orbit G (V i))) := by
      convert claim23 V i hS hP hm H hgrp P_order G_order hPrime
    have h₁ : i ∈ notdivset_orb V := by
      exact h₀
    exact h₁

--currently, notdivset_orb is all the sets whose orbits have size not divisible by p
--we need to whittle this d

lemma claim24_pt2 {G I : Type*} [Group G] {p n m : ℕ} [Fintype G] [Fintype I] [DecidableEq (X G p n)]
 (V : I → X G p n) (i : I)
    (hS : Fintype (stabilizer G (V i)))
    (hP : Fintype (V i))
    (H : Subgroup G) (hgrp : H = (V i).val) 
    (hm : p.Coprime m)
    (M : notdivset_orb V → Subgroup G)
    (hM : ∀ (j : notdivset_orb V), (M j : Set G) = (V j).val)
    (P_order : Fintype.card (V i).val = p^n)
    (G_order : Fintype.card G = m * p^n)
    (hPrime : Nat.Prime p) : ∀ (i j : notdivset_orb V), orbit G (V i) = orbit G (V j) → V i = V j := by
      intro x y
      have h₀ : orbit G (V x) = orbit G (V y) → (V x) ∈ orbit G (V y) := by
        intro z
        apply MulAction.orbit_eq_iff.mp z
      have h₁ : (V x) ∈ orbit G (V y) → ∃ (g : G), g • (V y) = (V x) := by
        intro z
        apply MulAction.mem_orbit_iff.mp z
      have h₂ : (1 : G) ∈ (V x).val := by
        apply?
