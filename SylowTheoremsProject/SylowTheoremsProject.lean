import SylowTheoremsProject.Imports
import SylowTheoremsProject.Skeleton_9&10
import SylowTheoremsProject.Lagrange
import SylowTheoremsProject.claim_2_orb_2
import SylowTheoremsProject.NumberTheory
import SylowTheoremsProject.OrbitStabilizer
import SylowTheoremsProject.Conclusion
import SylowTheoremsProject.Claim1
import SylowTheoremsProject.Bijectivity Statements

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

/-This returns errors when using Fintype
so I will keep it as Nat unless we need to change it-/
theorem sylow_one_mod_prime
  {G : Type _} [Group G] [Fintype G]
  {p : ℕ} (hp : p.Prime)
  (n m : ℕ)
  (hcard : Nat.card G = p ^ n * m)
  (hcop : IsCoprime p m) :
  ↑(Nat.card (Syl_p G p)) = (1:ZMod p) := by sorry
