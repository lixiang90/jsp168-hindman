import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.OrderOfElement

/-! Literal signed-integer falling products have a common modular period.
Finite-group powers respect that period, regardless of the magnitude or
sign of the multiplying integer coefficient. -/
namespace Hindman168
open scoped BigOperators

def signedFallingProduct (j : ℕ) (b : ℤ) : ℤ := ∏ r ∈ Finset.range j, (b-(r : ℤ))

theorem signed_falling_product_modEq (j : ℕ) {M b c : ℤ} (h : Int.ModEq M b c) :
    Int.ModEq M (signedFallingProduct j b) (signedFallingProduct j c) := by
  induction j with
  | zero => exact Int.ModEq.refl _
  | succ j ih =>
      simp only [signedFallingProduct, Finset.prod_range_succ] at ih ⊢
      exact ih.mul (h.sub (Int.ModEq.refl _))

theorem finite_group_zpow_modEq {G : Type*} [Group G] (g : G) {b c : ℤ}
    (h : Int.ModEq (Nat.card G : ℤ) b c) : g^b = g^c := by
  calc
    g^b = g^(b % (Nat.card G : ℤ)) := (zpow_mod_natCard g b).symm
    _ = g^(c % (Nat.card G : ℤ)) := congrArg (fun r : ℤ => g^r) h
    _ = g^c := zpow_mod_natCard g c

theorem finite_group_falling_powers_period {G : Type*} [Group G] (g : G) (j : ℕ) (m : ℤ)
    {b c : ℤ} (h : Int.ModEq (Nat.card G : ℤ) b c) :
    g^(m * signedFallingProduct j b) = g^(m * signedFallingProduct j c) :=
  finite_group_zpow_modEq g ((Int.ModEq.refl m).mul (signed_falling_product_modEq j h))

end Hindman168
