--skeleton 9 & 10
import SylowTheoremsProject.Imports
import SylowTheoremsProject.OrbitStabiliser
import SylowTheoremsProject.Claim1

--open Set
open Fintype
open Finset
universe u v

variable {G : Type*} [Group G] [Fintype G]
variable {p n : ℕ} [Fact p.Prime]

variable {G : Type*} [Group G] [Fintype G]
variable {p n : ℕ} [Fact p.Prime]

/--Step 5 for every `S : X G p n`, there exists `T` in the orbit of `S` such that `1 ∈ T`-/
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

variable {α : Type*} (I : Finset α) (p : ℕ)
--says p divides the order of each set in the sum indezed over range n

def icard {U : Type u} {I : Type v} [Fintype I]
{V : I → Set U} (i : I) (hV : ∀ (i : I), Fintype (V i))
: ℕ := Fintype.card (V i)

--skeleton (9)
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

variable {α : Type*} (I : Finset α) (p : ℕ) (Prime p)
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

--gives the subset J of the index I of the sum so that we can split the sum
-- into a sum over J, where p ∤ |Vⱼ| and a sum over I \ J where p | |Vᵢ|
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

/-unsure if we need
lemma rearrange_10 {U : Type u} {I : Type v} [Fintype I] (p : ℕ)
{V : I → Set U} (hV : ∀ (i : I), Fintype (V i))
(hdiv : ¬ (p ∣ ∑ᶠ (i : I), Fintype.card (V i))) :
 ∃ (J : Finset I), Nonempty J → ∀ (j : J), ¬ (p ∣ Fintype.card (V j))
  → ∀ (i : I), i ∉ J → (p ∣ Fintype.card (V i)) := by
  have h₀ : ∃ (J : Finset I), Nonempty J → ∀ (j : J), ¬ (p ∣ Fintype.card (V j)) := by
   exact notdiv_index_subset p hV hdiv
  sorry
  --have h₁ : {i : I | p ∣ Fintype.card (V i)} = {i : I | i ∉ J}
  --lean can;t work out what J is

-/
