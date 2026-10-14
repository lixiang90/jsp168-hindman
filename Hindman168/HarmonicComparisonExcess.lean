import Hindman168.CountableDomination
import Hindman168.PrimePowerUnitExcess
import Hindman168.HarmonicPowerComparison

/-!
# Original harmonic divisor draws and their actual CRT excess expectation

Actual independent harmonic raw draws are mapped to their row products.
The proved pointwise comparison is applied to these original PMFs, with
one factor (4 exp 3) per raw draw overall. The nonnegative CRT excess then
has finite expectation bounded by that global factor times the proved
comparison-law O(1/w) tail. There is no per-tested-prime domination cost.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def harmonicDivisorPMF {κ : Type*} [Fintype κ] (X : κ → ℕ) (W : ℕ)
    (hH : ∀ j, 0 < harmonicNormalizer (X j) W) : PMF ℕ :=
  (DiscreteProduct.piPMF (fun j => harmonicPMF (X j) W (hH j))).map (fun x => ∏ j, x j)

noncomputable def harmonicRowDivisorPMF {q : ℕ} {κ : Type*} [Fintype κ]
    (X : Fin q → κ → ℕ) (W : ℕ) (hH : ∀ i j, 0 < harmonicNormalizer (X i j) W) : PMF (Fin q → ℕ) :=
  DiscreteProduct.piPMF (fun i => harmonicDivisorPMF (X i) W (hH i))

theorem harmonicPMF_powerUnit_atom_domination (X : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hX : 2 ≤ X) (hW : (∏ p ∈ P, p) ≤ X)
    (hH : 0 < harmonicNormalizer X (∏ p ∈ P, p)) (hlog : 2 ≤ Real.log (X : ℝ))
    (hZ : powerUnitNormalizer (comparisonExponent X) 1 ≤ 2 * Real.log (X : ℝ)) (n : ℕ) :
    (harmonicPMF X (∏ p ∈ P, p) hH n).toReal ≤
      (4 * Real.exp 3) * (powerUnitPMF (comparisonExponent X)
        (comparisonExponent_gt_one hX) (∏ p ∈ P, p) n).toReal := by
  rw [harmonicPMF_apply, powerUnitPMF_apply,
    ENNReal.toReal_ofReal (harmonicWeight_nonneg hH n),
    ENNReal.toReal_ofReal (powerUnitProbability_nonneg (comparisonExponent_gt_one hX) _ n)]
  exact harmonicWeight_le_powerUnitProbability hX P hP hW hlog hZ n

theorem harmonicDivisorPMF_atom_domination {κ : Type*} [Fintype κ]
    (X : κ → ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hX : ∀ j, 2 ≤ X j) (hW : ∀ j, (∏ p ∈ P, p) ≤ X j)
    (hH : ∀ j, 0 < harmonicNormalizer (X j) (∏ p ∈ P, p))
    (hlog : ∀ j, 2 ≤ Real.log (X j : ℝ))
    (hZ : ∀ j, powerUnitNormalizer (comparisonExponent (X j)) 1 ≤ 2 * Real.log (X j : ℝ))
    (d : ℕ) :
    (harmonicDivisorPMF X (∏ p ∈ P, p) hH d).toReal ≤
      (4 * Real.exp 3) ^ Fintype.card κ *
        (comparisonDivisorPMF (fun j => comparisonExponent (X j))
          (fun j => comparisonExponent_gt_one (hX j)) (∏ p ∈ P, p) d).toReal := by
  apply DiscreteProduct.map_atom_domination _ _ _ (by positivity)
  intro x
  exact DiscreteProduct.piPMF_atom_domination _ _ _ (by positivity)
    (fun j n => harmonicPMF_powerUnit_atom_domination (X j) P hP (hX j) (hW j)
      (hH j) (hlog j) (hZ j) n) x

theorem harmonicRowDivisorPMF_atom_domination {q : ℕ} {κ : Type*} [Fintype κ]
    (X : Fin q → κ → ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hX : ∀ i j, 2 ≤ X i j) (hW : ∀ i j, (∏ p ∈ P, p) ≤ X i j)
    (hH : ∀ i j, 0 < harmonicNormalizer (X i j) (∏ p ∈ P, p))
    (hlog : ∀ i j, 2 ≤ Real.log (X i j : ℝ))
    (hZ : ∀ i j, powerUnitNormalizer (comparisonExponent (X i j)) 1 ≤ 2 * Real.log (X i j : ℝ))
    (d : Fin q → ℕ) :
    (harmonicRowDivisorPMF X (∏ p ∈ P, p) hH d).toReal ≤
      (4 * Real.exp 3) ^ (Fintype.card κ * q) *
        (comparisonRowPMF (fun i j => comparisonExponent (X i j))
          (fun i j => comparisonExponent_gt_one (hX i j)) (∏ p ∈ P, p) d).toReal := by
  have h := DiscreteProduct.piPMF_atom_domination
    (fun i => harmonicDivisorPMF (X i) (∏ p ∈ P, p) (hH i))
    (fun i => comparisonDivisorPMF (fun j => comparisonExponent (X i j))
      (fun j => comparisonExponent_gt_one (hX i j)) (∏ p ∈ P, p))
    ((4 * Real.exp 3) ^ Fintype.card κ) (by positivity)
    (fun i d => harmonicDivisorPMF_atom_domination (X i) P hP (hX i) (hW i) (hH i) (hlog i) (hZ i) d) d
  simpa only [harmonicRowDivisorPMF, comparisonRowPMF, Fintype.card_fin, ← pow_mul] using h

theorem harmonicRow_CRT_excess_summable {q n : ℕ} {κ : Type*} [Fintype κ]
    (X : Fin q → κ → ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hX : ∀ i j, 2 ≤ X i j) (hW : ∀ i j, (∏ p ∈ P, p) ≤ X i j)
    (hH : ∀ i j, 0 < harmonicNormalizer (X i j) (∏ p ∈ P, p))
    (hlog : ∀ i j, 2 ≤ Real.log (X i j : ℝ))
    (hZ : ∀ i j, powerUnitNormalizer (comparisonExponent (X i j)) 1 ≤ 2 * Real.log (X i j : ℝ))
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hc : ∀ p ∈ S, p.Coprime (∏ p ∈ P, p))
    (D : Finset (MvPolynomial (Fin n) ℤ)) :
    Summable (fun d => (harmonicRowDivisorPMF X (∏ p ∈ P, p) hH d).toReal *
      comparisonPrimePowerCRTIntegrand S hS D d) := by
  apply DiscreteProduct.weighted_summable_of_domination _ _ _ (by positivity)
    (harmonicRowDivisorPMF_atom_domination X P hP hX hW hH hlog hZ)
    _ (fun d => by rw [comparisonPrimePowerCRTIntegrand_eq]; exact comparisonPrimeExcessIntegrand_nonneg S hS D d)
  exact comparisonPrimePowerCRTIntegrand_summable
    (fun i j => comparisonExponent (X i j)) (fun i j => comparisonExponent_gt_one (hX i j))
    (∏ p ∈ P, p) S hS hc D

theorem harmonicRow_CRT_excess_expectation_bound {q n : ℕ} {κ : Type*} [Fintype κ]
    (X : Fin q → κ → ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hX : ∀ i j, 2 ≤ X i j) (hW : ∀ i j, (∏ p ∈ P, p) ≤ X i j)
    (hH : ∀ i j, 0 < harmonicNormalizer (X i j) (∏ p ∈ P, p))
    (hlog : ∀ i j, 2 ≤ Real.log (X i j : ℝ))
    (hZ : ∀ i j, powerUnitNormalizer (comparisonExponent (X i j)) 1 ≤ 2 * Real.log (X i j : ℝ))
    (w : ℕ) (hw : 0 < w) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hc : ∀ p ∈ S, p.Coprime (∏ p ∈ P, p)) (hgreater : ∀ p ∈ S, w < p)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    (hcut : D.sup integerPolynomialCoeffSize ≤ w)
    (hsmall : localExcessPrimeTestConstant (Fintype.card κ) q D ≤ (w : ℝ)) :
    DiscreteProduct.expectation (harmonicRowDivisorPMF X (∏ p ∈ P, p) hH)
        (comparisonPrimePowerCRTIntegrand S hS D) ≤
      (4 * Real.exp 3) ^ (Fintype.card κ * q) *
        (2 * localExcessPrimeTestConstant (Fintype.card κ) q D / (w : ℝ)) := by
  have hdom := DiscreteProduct.expectation_le_of_domination
    (harmonicRowDivisorPMF X (∏ p ∈ P, p) hH)
    (comparisonRowPMF (fun i j => comparisonExponent (X i j))
      (fun i j => comparisonExponent_gt_one (hX i j)) (∏ p ∈ P, p))
    ((4 * Real.exp 3) ^ (Fintype.card κ * q)) (by positivity)
    (harmonicRowDivisorPMF_atom_domination X P hP hX hW hH hlog hZ)
    (comparisonPrimePowerCRTIntegrand S hS D)
    (fun d => by rw [comparisonPrimePowerCRTIntegrand_eq]; exact comparisonPrimeExcessIntegrand_nonneg S hS D d)
    (comparisonPrimePowerCRTIntegrand_summable
      (fun i j => comparisonExponent (X i j)) (fun i j => comparisonExponent_gt_one (hX i j))
      (∏ p ∈ P, p) S hS hc D)
  exact hdom.trans (mul_le_mul_of_nonneg_left
    (comparisonPrimePowerCRT_expectation_tail
      (fun i j => comparisonExponent (X i j)) (fun i j => comparisonExponent_gt_one (hX i j))
      (∏ p ∈ P, p) w hw S hS hc hgreater D hD hcut hsmall).2 (by positivity))

end Hindman168
