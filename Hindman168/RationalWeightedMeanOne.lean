import Hindman168.RationalResidueRows
import Hindman168.SquarefreeWeightedLinearForms

/-!
# Weighted mean-one for integer-valued rational linear forms

The masks are the original integer-multiple masks on rational arguments.
An exact support-sensitive identity clears the unit denominators. Primitive
and independent rational residue rows then imply the integer row hypotheses
of the already proved estimate. The true original base modulus is unchanged.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem rational_weighted_masks_expectation_eq {q d : ℕ} {α : Type*}
    (ρ : Fin q → Mass ℕ) (μ : Mass α) (base : α → Mass (Fin d → ℤ))
    (c : α → Fin q → Fin d → ℚ) (den : α → Fin q → ℕ)
    (b : α → Fin q → Fin d → ℤ) (E : α → Prop)
    (hclear : ∀ x, E x → ∀ u j, (den x u : ℚ) * c x u j = (b x u j : ℚ))
    (hvalue : ∀ x, E x → ∀ y ∈ (base x).support, ∀ u,
      ∃ z : ℤ, (∑ j, c x u j * (y j : ℚ)) = (z : ℚ))
    (hunit : ∀ x, E x → ∀ u, ∀ k ∈ (ρ u).support, (den x u).Coprime k) :
    expectation μ (fun x => if E x then expectation (base x)
      (fun y => ∏ u, rationalDivisorMask (ρ u) (∑ j, c x u j * (y j : ℚ))) else 0) =
    expectation μ (fun x => if E x then expectation (base x)
      (fun y => ∏ u, integerDivisorMask (ρ u) (∑ j, b x u j * y j)) else 0) := by
  apply expectation_congr_support
  intro x _
  by_cases hx : E x
  · simp only [if_pos hx]
    apply expectation_congr_support
    intro y hy
    exact Finset.prod_congr rfl (fun u _ => rational_row_mask_clear (ρ u) (c x u)
      (den x u) (b x u) (hclear x hx u) y (hvalue x hx y hy u) (hunit x hx u))
  · simp only [if_neg hx]

theorem squarefree_weighted_rational_linear_forms_mean_one_error {q d n : ℕ} {α : Type*}
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (ρ : Fin q → Mass ℕ)
    (hρ : ∀ u k, 0 ≤ ρ u k) (htρ : ∀ u, total (ρ u) = 1)
    (μ : Mass α) (hμ : ∀ x, 0 ≤ μ x) (htμ : total μ = 1)
    (base : α → Mass (Fin d → ℤ))
    (c : α → Fin q → Fin d → ℚ) (den : α → Fin q → ℕ)
    (b : α → Fin q → Fin d → ℤ) (E : α → Prop)
    (hclear : ∀ x, E x → ∀ u j, (den x u : ℚ) * c x u j = (b x u j : ℚ))
    (hvalue : ∀ x, E x → ∀ y ∈ (base x).support, ∀ u,
      ∃ z : ℤ, (∑ j, c x u j * (y j : ℚ)) = (z : ℚ))
    (hunit : ∀ x, E x → ∀ u, ∀ k ∈ (ρ u).support, (den x u).Coprime k)
    (D : Finset (MvPolynomial (Fin n) ℤ))
    (stat : α → Fin n → ZMod (squarefreeCRTModulus S))
    (V : ℕ) (εbase εprime : ℝ) (hεbase : 0 ≤ εbase)
    (hs : ∀ k ∈ (piMass ρ).support, ∀ u, k u ≠ 0 ∧ k u ≤ V ∧ (k u).primeFactors ⊆ S)
    (hprimeunit : ∀ x, E x → ∀ p : S, ∀ u, (den x u).Coprime (p : ℕ))
    (hprimitive : ∀ x, E x → ∀ p : S, ∀ u, ∃ j, unitDenominatorRow (p : ℕ) (den x u) (b x u) j ≠ 0)
    (hindependent : ∀ k ∈ (piMass ρ).support, ∀ x, E x → ∀ p : S,
      (∑ u, (k u).factorization p) ≠ 0 → ¬ squarefreeCRTBadEvent S hS D (stat x) p →
        ∀ u v, u ≠ v → LinearIndependent (ZMod (p : ℕ))
          ![(fun j => unitDenominatorRow (p : ℕ) (den x u) (b x u) j), (fun j => unitDenominatorRow (p : ℕ) (den x v) (b x v) j)])
    (hprime : distance (μ.mapDomain stat) (squarefreeCRTUniformParameterMass S hS n) ≤ εprime)
    (hbase : ∀ x, E x → ∀ k, (hk : k ∈ (piMass ρ).support) →
      letI : NeZero (∏ u, k u) := ⟨Finset.prod_ne_zero_iff.mpr (fun u _ => (hs k hk u).1)⟩
      distance ((base x).mapDomain (fun y j => (y j : ZMod (∏ u, k u))))
        (uniformFintypeMass (Fin d → ZMod (∏ u, k u))) ≤ εbase) :
    |expectation μ (fun x => if E x then expectation (base x)
        (fun y => ∏ u, rationalDivisorMask (ρ u) (∑ j, c x u j * (y j : ℚ))) else 0) - event μ E| ≤
      expectation (piMass ρ) (comparisonPrimePowerCRTIntegrand S hS D) +
        ((V ^ q : ℕ) : ℝ) * (εbase + εprime) := by
  rw [rational_weighted_masks_expectation_eq ρ μ base c den b E hclear hvalue hunit]
  apply squarefree_weighted_integer_linear_forms_mean_one_error S hS ρ hρ htρ μ hμ htμ
    base b E D stat V εbase εprime hεbase hs
  · intro x hx p u
    exact (unitDenominatorRow_primitive_iff (hprimeunit x hx p u) (b x u)).mp
      (hprimitive x hx p u)
  · intro k hk x hx p he hbad u v huv
    exact (unitDenominatorRow_pairIndependent_iff (hprimeunit x hx p u)
      (hprimeunit x hx p v) (b x u) (b x v)).mp
        (hindependent k hk x hx p he hbad u v huv)
  · exact hprime
  · exact hbase

end Hindman168
