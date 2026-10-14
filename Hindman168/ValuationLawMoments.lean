import Hindman168.LocalExcessValuationMoments
import Hindman168.ComparisonPrimeExcessExpectation

/-!
# Genuine valuation moments from the proved atom majorant

The finite-cell estimates apply to any actual PMF bounded by the explicit
valuation weight. Finite partial sums prove summability and the original
unit-polynomial expectation has its uniform O(p^-2) bound. No desired
moment estimate is assumed as an input.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem valuationLaw_bad_finite_bound {q : ℕ} (μ : PMF (Fin q → ℕ)) (p b : ℕ) [NeZero p]
    (hp : 2 ≤ p) (hm : ∀ a, (μ a).toReal ≤ rowValuationWeight p b a) (T : Finset (Fin q → ℕ)) :
    (∑ a ∈ T, (μ a).toReal * localExcessBeta p a True) ≤
      polynomialGeometricConstant ((b + 1) * q) / (p : ℝ) :=
  (Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_right (hm a) (localExcessBeta_nonneg p a True))).trans
    (finite_localExcessBeta_bad_weight_bound p b q hp T)

theorem valuationLaw_good_finite_bound {q : ℕ} (μ : PMF (Fin q → ℕ)) (p b : ℕ) [NeZero p]
    (hp : 2 ≤ p) (hm : ∀ a, (μ a).toReal ≤ rowValuationWeight p b a) (T : Finset (Fin q → ℕ)) :
    (∑ a ∈ T, (μ a).toReal * localExcessBeta p a False) ≤
      (q : ℝ) * (polynomialGeometricConstant b * polynomialGeometricConstant ((b + 1) * q) / (p : ℝ) ^ 2) :=
  (Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_right (hm a) (localExcessBeta_nonneg p a False))).trans
    (finite_localExcessBeta_good_weight_bound p b q hp T)

theorem valuationLaw_bad_summable {q : ℕ} (μ : PMF (Fin q → ℕ)) (p b : ℕ) [NeZero p]
    (hp : 2 ≤ p) (hm : ∀ a, (μ a).toReal ≤ rowValuationWeight p b a) :
    Summable (fun a => (μ a).toReal * localExcessBeta p a True) :=
  summable_of_sum_le (fun a => mul_nonneg ENNReal.toReal_nonneg (localExcessBeta_nonneg p a True))
    (valuationLaw_bad_finite_bound μ p b hp hm)

theorem valuationLaw_good_summable {q : ℕ} (μ : PMF (Fin q → ℕ)) (p b : ℕ) [NeZero p]
    (hp : 2 ≤ p) (hm : ∀ a, (μ a).toReal ≤ rowValuationWeight p b a) :
    Summable (fun a => (μ a).toReal * localExcessBeta p a False) :=
  summable_of_sum_le (fun a => mul_nonneg ENNReal.toReal_nonneg (localExcessBeta_nonneg p a False))
    (valuationLaw_good_finite_bound μ p b hp hm)

theorem valuationLaw_bad_expectation_bound {q : ℕ} (μ : PMF (Fin q → ℕ)) (p b : ℕ) [NeZero p]
    (hp : 2 ≤ p) (hm : ∀ a, (μ a).toReal ≤ rowValuationWeight p b a) :
    DiscreteProduct.expectation μ (fun a => localExcessBeta p a True) ≤
      polynomialGeometricConstant ((b + 1) * q) / (p : ℝ) :=
  (valuationLaw_bad_summable μ p b hp hm).tsum_le_of_sum_le (valuationLaw_bad_finite_bound μ p b hp hm)

theorem valuationLaw_good_expectation_bound {q : ℕ} (μ : PMF (Fin q → ℕ)) (p b : ℕ) [NeZero p]
    (hp : 2 ≤ p) (hm : ∀ a, (μ a).toReal ≤ rowValuationWeight p b a) :
    DiscreteProduct.expectation μ (fun a => localExcessBeta p a False) ≤
      (q : ℝ) * (polynomialGeometricConstant b * polynomialGeometricConstant ((b + 1) * q) / (p : ℝ) ^ 2) :=
  (valuationLaw_good_summable μ p b hp hm).tsum_le_of_sum_le (valuationLaw_good_finite_bound μ p b hp hm)

theorem valuationLaw_primeUnitBeta_summable {q n : ℕ} (μ : PMF (Fin q → ℕ)) (p b : ℕ) [NeZero p]
    (hp : 2 ≤ p) (hm : ∀ a, (μ a).toReal ≤ rowValuationWeight p b a)
    (D : Finset (MvPolynomial (Fin n) ℤ)) :
    Summable (fun a => (μ a).toReal * primeUnitBetaMean p D a) := by
  let δ := event (piMass (fun _ : Fin n => zmodUnitUniformMass p)) (unitPolynomialTestEvent D p)
  have h := ((valuationLaw_bad_summable μ p b hp hm).mul_left δ).add
    ((valuationLaw_good_summable μ p b hp hm).mul_left (1 - δ))
  apply h.congr
  intro a
  rw [primeUnitBetaMean, localExcessBeta_unit_expectation]
  dsimp only [δ]
  ring

theorem valuationLaw_primeUnitBeta_expectation_decomposition {q n : ℕ}
    (μ : PMF (Fin q → ℕ)) (p b : ℕ) [NeZero p]
    (hp : 2 ≤ p) (hm : ∀ a, (μ a).toReal ≤ rowValuationWeight p b a)
    (D : Finset (MvPolynomial (Fin n) ℤ)) :
    DiscreteProduct.expectation μ (primeUnitBetaMean p D) =
      event (piMass (fun _ : Fin n => zmodUnitUniformMass p)) (unitPolynomialTestEvent D p) *
        DiscreteProduct.expectation μ (fun a => localExcessBeta p a True) +
      (1 - event (piMass (fun _ : Fin n => zmodUnitUniformMass p)) (unitPolynomialTestEvent D p)) *
        DiscreteProduct.expectation μ (fun a => localExcessBeta p a False) := by
  unfold DiscreteProduct.expectation
  simp_rw [primeUnitBetaMean, localExcessBeta_unit_expectation]
  have he (m B G δ : ℝ) : m * (δ * B + (1 - δ) * G) = δ * (m * B) + (1 - δ) * (m * G) := by ring
  simp_rw [he]
  rw [Summable.tsum_add ((valuationLaw_bad_summable μ p b hp hm).mul_left _)
    ((valuationLaw_good_summable μ p b hp hm).mul_left _), tsum_mul_left, tsum_mul_left]

theorem valuationLaw_primeUnitBeta_expectation_bound {q n : ℕ}
    (μ : PMF (Fin q → ℕ)) (p b : ℕ) [NeZero p] (hp : p.Prime)
    (hm : ∀ a, (μ a).toReal ≤ rowValuationWeight p b a)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    (hcut : D.sup integerPolynomialCoeffSize < p) :
    DiscreteProduct.expectation μ (primeUnitBetaMean p D) ≤ localExcessPrimeTestConstant b q D / (p : ℝ) ^ 2 := by
  let δ := event (piMass (fun _ : Fin n => zmodUnitUniformMass p)) (unitPolynomialTestEvent D p)
  have hδ : 0 ≤ δ := event_nonneg _ _ (piMass_nonneg _ (fun _ => zmodUnitUniformMass_nonneg p))
  have hb := valuationLaw_bad_expectation_bound μ p b hp.two_le hm
  have hg := valuationLaw_good_expectation_bound μ p b hp.two_le hm
  have hbn : 0 ≤ DiscreteProduct.expectation μ (fun a => localExcessBeta p a True) :=
    tsum_nonneg (fun a => mul_nonneg ENNReal.toReal_nonneg (localExcessBeta_nonneg p a True))
  have hgn : 0 ≤ DiscreteProduct.expectation μ (fun a => localExcessBeta p a False) :=
    tsum_nonneg (fun a => mul_nonneg ENNReal.toReal_nonneg (localExcessBeta_nonneg p a False))
  rw [valuationLaw_primeUnitBeta_expectation_decomposition μ p b hp.two_le hm D]
  change δ * _ + (1 - δ) * _ ≤ _
  have ht := integerPolynomial_family_prime_unit_uniform_bound hp D hD hcut
  calc
    _ ≤ (2 * (∑ f ∈ D, ∑ i, (f.degreeOf i : ℝ)) / (p : ℝ)) *
        (polynomialGeometricConstant ((b + 1) * q) / (p : ℝ)) +
        (q : ℝ) * (polynomialGeometricConstant b * polynomialGeometricConstant ((b + 1) * q) / (p : ℝ) ^ 2) := by
      apply add_le_add
      · exact mul_le_mul ht hb hbn (by positivity)
      · exact (mul_le_mul_of_nonneg_right (show 1 - δ ≤ 1 by linarith) hgn).trans
          (by simpa only [one_mul] using hg)
    _ = _ := by
      unfold localExcessPrimeTestConstant
      have hpn : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      field_simp

end Hindman168
