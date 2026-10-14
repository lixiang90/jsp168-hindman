import Hindman168.PrincipalBoundedCounts
import Mathlib.Tactic

/-!
# Pointwise model mass from alignment and product-chain selection

The model factors here are the original principal bounded-count
integrand, including every nonempty product mask. Singleton sum factors
are one. This makes the lower bound independent of a fixed samplewise
choice of chain or color.
-/

namespace Hindman168
open scoped BigOperators Classical

/-- Once alignment raises all nonsingleton rows and product selection
makes all product masks one, the exact model integrand has positive size. -/
theorem principal_model_integrand_lower_bound {n m M r : ℕ}
    (C : PrincipalCoordinateChain n (m+1)) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (a : Fin (m+1) → ℚ)
    (χ : ℕ → Fin r) (κ : Fin r) (w : ℕ)
    (S : Fin (m+1) → ℤ → ℝ) (z : Fin (m+1) → ℕ)
    (hz : ∀ i, 0 < z i) (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hrows : ∀ V : NonemptyColumnSubset (m+1), 2 ≤ V.val.card →
      τ ≤ S (V.val.max' V.property)
        (maskSubsetIntegerForm (C.coefficient M e a w) V (fun k => (z k : ℤ))))
    (hproducts : ∀ V : Finset (Fin (m+1)), V.Nonempty →
      χ (∏ k ∈ V, C.coefficient M e a w k * z k) = κ) :
    τ ^ Fintype.card (NonemptyColumnSubset (m+1)) ≤
      principalBoundedCountIntegrand C M e a w S
        (principalColorProductMask C M e a χ κ w) (fun k => (z k : ℤ)) := by
  have hmask : ∀ V ∈ (Finset.univ : Finset (Fin (m+1))).powerset.erase ∅,
      principalColorProductMask C M e a χ κ w V (∏ k ∈ V, (z k : ℤ)) = 1 := by
    intro V hV
    have hne : V.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hV).1
    rw [← Nat.cast_prod, principalColorProductMask_natural C e heM a χ κ w V z
      (fun k _ => hz k), if_pos (hproducts V hne)]
  unfold principalBoundedCountIntegrand
  rw [Finset.prod_eq_one hmask, mul_one]
  have hh : (∏ _V : NonemptyColumnSubset (m+1), τ) ≤
      ∏ V : NonemptyColumnSubset (m+1), if 2 ≤ V.val.card then
        S (V.val.max' V.property)
          (maskSubsetIntegerForm (C.coefficient M e a w) V (fun k => (z k : ℤ))) else 1 := by
    apply Finset.prod_le_prod (fun _ _ => hτ)
    intro V _
    split_ifs with hV
    · exact hrows V hV
    · exact hτ1
  simpa only [Finset.prod_const, Finset.card_univ] using hh

/-- Calibration-good singleton centers and the exact alignment implication
supply the nonsingleton row lower bounds, rather than postulating them. -/
theorem principal_model_integrand_lower_bound_of_alignment {n m M r : ℕ}
    (C : PrincipalCoordinateChain n (m+1)) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (a : Fin (m+1) → ℚ)
    (χ : ℕ → Fin r) (κ : Fin r) (w : ℕ)
    (S : Fin (m+1) → ℤ → ℝ) (z : Fin (m+1) → ℕ)
    (hz : ∀ i, 0 < z i) (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hcenters : ∀ i, 2 * τ < S i (z i))
    (halign : ∀ V : NonemptyColumnSubset (m+1), 2 ≤ V.val.card →
      2 * τ < S (V.val.max' V.property) (z (V.val.max' V.property)) →
      τ < S (V.val.max' V.property)
        (maskSubsetIntegerForm (C.coefficient M e a w) V (fun k => (z k : ℤ))))
    (hproducts : ∀ V : Finset (Fin (m+1)), V.Nonempty →
      χ (∏ k ∈ V, C.coefficient M e a w k * z k) = κ) :
    τ ^ Fintype.card (NonemptyColumnSubset (m+1)) ≤
      principalBoundedCountIntegrand C M e a w S
        (principalColorProductMask C M e a χ κ w) (fun k => (z k : ℤ)) :=
  principal_model_integrand_lower_bound C e heM a χ κ w S z hz τ hτ hτ1
    (fun V hV => (halign V hV (hcenters _)).le) hproducts

end Hindman168
