import Hindman168.VariableHarmonicRows
import Hindman168.WeightedLinearFormsMeanOne

/-!
# Complete weighted estimate with at most b factors per row

Rows have different finite raw index families, including empty ones.
The actual independent mask expansion and residue errors are unchanged.
The genuine global harmonic excess cost uses the total actual raw count,
while its local moment constant uses only the common bound b.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem variable_harmonic_integer_linear_forms_mean_one_error {q d n : ℕ} {α : Type*} {κ : Fin q → Type*} [∀ i, Fintype (κ i)]
    (X : ∀ i, κ i → ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hX : ∀ i j, 2 ≤ X i j) (hW : ∀ i j, (∏ p ∈ P, p) ≤ X i j)
    (hH : ∀ i j, 0 < harmonicNormalizer (X i j) (∏ p ∈ P, p))
    (hlog : ∀ i j, 2 ≤ Real.log (X i j : ℝ))
    (hZ : ∀ i j, powerUnitNormalizer (comparisonExponent (X i j)) 1 ≤ 2 * Real.log (X i j : ℝ))
    (b : ℕ) (hb : ∀ i, Fintype.card (κ i) ≤ b) (w : ℕ) (hw : 0 < w) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hc : ∀ p ∈ S, p.Coprime (∏ p ∈ P, p)) (hgreater : ∀ p ∈ S, w < p)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    (hcut : D.sup integerPolynomialCoeffSize ≤ w)
    (hsmall : localExcessPrimeTestConstant (b) q D ≤ (w : ℝ))
    (V : ℕ) (hbound : ∀ i, (∏ j, (X i j) ^ 2) ≤ V)
    (hcover : ∀ m, 0 < m → m ≤ V → m.Coprime (∏ p ∈ P, p) → m.primeFactors ⊆ S)
    (μ : Mass α) (hμ : ∀ x, 0 ≤ μ x) (htμ : total μ = 1)
    (base : α → Mass (Fin d → ℤ)) (c : α → Fin q → Fin d → ℤ) (E : α → Prop)
    (stat : ∀ k : Fin q → ℕ, α → Fin n → ZMod (rowCRTModulus S k))
    (εbase εprime : ℝ) (hεbase : 0 ≤ εbase)
    (hprimitive : ∀ x, E x → ∀ p : S, ∀ u, ∃ j, (c x u j : ZMod (p : ℕ)) ≠ 0)
    (hindependent : ∀ k ∈ (variableHarmonicRowDivisorMass X (∏ p ∈ P, p)).support,
      ∀ x, E x → ∀ p : S, (∑ u, (k u).factorization p) ≠ 0 →
        ¬ rowCRTBadEvent S hS k D (stat k x) p →
        ∀ u v, u ≠ v → LinearIndependent (ZMod (p : ℕ))
          ![(fun j => (c x u j : ZMod (p : ℕ))), (fun j => (c x v j : ZMod (p : ℕ)))])
    (hprime : ∀ k ∈ (variableHarmonicRowDivisorMass X (∏ p ∈ P, p)).support,
      distance (μ.mapDomain (stat k)) (rowCRTUniformParameterMass S hS k n) ≤ εprime)
    (hbase : ∀ x, E x → ∀ k, (hk : k ∈ (variableHarmonicRowDivisorMass X (∏ p ∈ P, p)).support) →
      letI : NeZero (∏ u, k u) := ⟨Finset.prod_ne_zero_iff.mpr
        (fun u _ => (variableHarmonicRowDivisorMass_support X (∏ p ∈ P, p) hX hk u).1.ne')⟩
      distance ((base x).mapDomain (fun y j => (y j : ZMod (∏ u, k u))))
        (uniformFintypeMass (Fin d → ZMod (∏ u, k u))) ≤ εbase) :
    |expectation μ (fun x => if E x then expectation (base x)
        (fun y => ∏ u, integerDivisorMask (harmonicDivisorMass (X u) (∏ p ∈ P, p))
          (∑ j, c x u j * y j)) else 0) - event μ E| ≤
      (4 * Real.exp 3) ^ (∑ i, Fintype.card (κ i)) *
        (2 * localExcessPrimeTestConstant (b) q D / (w : ℝ)) +
          ((V ^ q : ℕ) : ℝ) * (εbase + εprime) := by
  have hs (k : Fin q → ℕ) (hk : k ∈ (variableHarmonicRowDivisorMass X (∏ p ∈ P, p)).support) (u : Fin q) :
      k u ≠ 0 ∧ k u ≤ V ∧ (k u).primeFactors ⊆ S := by
    have hu := variableHarmonicRowDivisorMass_support X (∏ p ∈ P, p) hX hk u
    have hb := hu.2.1.trans (hbound u)
    exact ⟨hu.1.ne', hb, hcover (k u) hu.1 hb hu.2.2⟩
  have h := weighted_integer_linear_forms_mean_one_error S hS
    (fun u => harmonicDivisorMass (X u) (∏ p ∈ P, p))
    (fun u => harmonicDivisorMass_nonneg (X u) (∏ p ∈ P, p) (hH u))
    (fun u => harmonicDivisorMass_total (X u) (∏ p ∈ P, p) (hH u))
    μ hμ htμ base c E D stat V εbase εprime hεbase hs hprimitive hindependent hprime hbase
  have hm := variableHarmonicRow_CRT_excess_expectation_bound X P hP hX hW hH hlog hZ
    b w hb hw S hS hc hgreater D hD hcut hsmall
  rw [← variableHarmonicRowDivisorMass_expectation X (∏ p ∈ P, p) hH] at hm
  exact h.trans (add_le_add_left hm _)


end Hindman168
