import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.RingTheory.Coprime.Basic
/-These imports will be tidied, once I sort the import file-/

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
  ↑(Nat.card (Syl_p G p)) = 1 := by sorry
