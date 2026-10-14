import Hindman168.VariableComparisonExcess
import Hindman168.HarmonicDivisorMass

/-!
# Actual harmonic rows with different raw cardinalities

Finite independent row-product masses have their exact original PMFs
and supports. The genuine joint comparison cost is (4 exp 3) raised to
the total number of actual raw draws. A bound of b factors in each row
controls the local moment constant and this cost by (4 exp 3)^(bq).
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def variableHarmonicRowDivisorMass {q : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (X : ∀ i, κ i → ℕ) (W : ℕ) : Mass (Fin q → ℕ) :=
  piMass (fun i => harmonicDivisorMass (X i) W)

noncomputable def variableHarmonicRowDivisorPMF {q : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (X : ∀ i, κ i → ℕ) (W : ℕ)
    (hH : ∀ i j, 0 < harmonicNormalizer (X i j) W) : PMF (Fin q → ℕ) :=
  DiscreteProduct.piPMF (fun i => harmonicDivisorPMF (X i) W (hH i))

theorem variableHarmonicRowDivisorMass_nonneg {q : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (X : ∀ i, κ i → ℕ) (W : ℕ)
    (hH : ∀ i j, 0 < harmonicNormalizer (X i j) W) (k : Fin q → ℕ) :
    0 ≤ variableHarmonicRowDivisorMass X W k :=
  piMass_nonneg _ (fun i => harmonicDivisorMass_nonneg (X i) W (hH i)) k

theorem variableHarmonicRowDivisorMass_total {q : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (X : ∀ i, κ i → ℕ) (W : ℕ)
    (hH : ∀ i j, 0 < harmonicNormalizer (X i j) W) :
    total (variableHarmonicRowDivisorMass X W) = 1 :=
  piMass_total_one _ (fun i => harmonicDivisorMass_total (X i) W (hH i))

theorem variableHarmonicRowDivisorPMF_eq_toPMF {q : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (X : ∀ i, κ i → ℕ) (W : ℕ)
    (hH : ∀ i j, 0 < harmonicNormalizer (X i j) W) :
    variableHarmonicRowDivisorPMF X W hH = toPMF (variableHarmonicRowDivisorMass X W)
      (variableHarmonicRowDivisorMass_nonneg X W hH) (variableHarmonicRowDivisorMass_total X W hH) := by
  unfold variableHarmonicRowDivisorPMF variableHarmonicRowDivisorMass
  simp only [harmonicDivisorPMF_eq_toPMF]
  rw [← toPMF_piMass]

theorem variableHarmonicRowDivisorMass_support {q : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (X : ∀ i, κ i → ℕ) (W : ℕ) (hX : ∀ i j, 2 ≤ X i j)
    {k : Fin q → ℕ} (hk : k ∈ (variableHarmonicRowDivisorMass X W).support) (i : Fin q) :
    0 < k i ∧ k i ≤ ∏ j, (X i j) ^ 2 ∧ (k i).Coprime W := by
  classical
  have hne := Finsupp.mem_support_iff.mp hk
  change piMass (fun i => harmonicDivisorMass (X i) W) k ≠ 0 at hne
  rw [piMass_apply] at hne
  exact harmonicDivisorMass_support (X i) W (hX i)
    (Finsupp.mem_support_iff.mpr (Finset.prod_ne_zero_iff.mp hne i (Finset.mem_univ i)))

theorem variableHarmonicRowDivisorMass_expectation {q : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (X : ∀ i, κ i → ℕ) (W : ℕ)
    (hH : ∀ i j, 0 < harmonicNormalizer (X i j) W) (f : (Fin q → ℕ) → ℝ) :
    expectation (variableHarmonicRowDivisorMass X W) f =
      DiscreteProduct.expectation (variableHarmonicRowDivisorPMF X W hH) f := by
  rw [variableHarmonicRowDivisorPMF_eq_toPMF, toPMF_expectation]

theorem variableHarmonicRowDivisorPMF_atom_domination {q : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (X : ∀ i, κ i → ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hX : ∀ i j, 2 ≤ X i j) (hW : ∀ i j, (∏ p ∈ P, p) ≤ X i j)
    (hH : ∀ i j, 0 < harmonicNormalizer (X i j) (∏ p ∈ P, p))
    (hlog : ∀ i j, 2 ≤ Real.log (X i j : ℝ))
    (hZ : ∀ i j, powerUnitNormalizer (comparisonExponent (X i j)) 1 ≤ 2 * Real.log (X i j : ℝ))
    (k : Fin q → ℕ) :
    (variableHarmonicRowDivisorPMF X (∏ p ∈ P, p) hH k).toReal ≤
      (4 * Real.exp 3) ^ (∑ i, Fintype.card (κ i)) *
        (variableComparisonRowPMF (fun i j => comparisonExponent (X i j))
          (fun i j => comparisonExponent_gt_one (hX i j)) (∏ p ∈ P, p) k).toReal := by
  rw [variableHarmonicRowDivisorPMF, variableComparisonRowPMF,
    DiscreteProduct.piPMF_apply, DiscreteProduct.piPMF_apply, ENNReal.toReal_prod, ENNReal.toReal_prod]
  calc
    _ ≤ ∏ i, ((4 * Real.exp 3) ^ Fintype.card (κ i) *
        (comparisonDivisorPMF (fun j => comparisonExponent (X i j))
          (fun j => comparisonExponent_gt_one (hX i j)) (∏ p ∈ P, p) (k i)).toReal) :=
      Finset.prod_le_prod (fun _ _ => ENNReal.toReal_nonneg)
        (fun i _ => harmonicDivisorPMF_atom_domination (X i) P hP (hX i) (hW i) (hH i) (hlog i) (hZ i) (k i))
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

theorem variable_raw_count_le {q : ℕ} {κ : Fin q → Type*} [∀ i, Fintype (κ i)]
    (b : ℕ) (hb : ∀ i, Fintype.card (κ i) ≤ b) : (∑ i, Fintype.card (κ i)) ≤ b * q := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm] using h

theorem variable_raw_comparison_cost_le {q : ℕ} {κ : Fin q → Type*} [∀ i, Fintype (κ i)]
    (b : ℕ) (hb : ∀ i, Fintype.card (κ i) ≤ b) :
    (4 * Real.exp 3) ^ (∑ i, Fintype.card (κ i)) ≤ (4 * Real.exp 3) ^ (b * q) := by
  have h : 1 ≤ 4 * Real.exp 3 := by
    have h3 : (1 : ℝ) ≤ Real.exp 3 := Real.one_le_exp_iff.mpr (by norm_num)
    linarith
  exact pow_le_pow_right₀ h (variable_raw_count_le b hb)

theorem variableHarmonicRow_CRT_excess_summable {q n : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (X : ∀ i, κ i → ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hX : ∀ i j, 2 ≤ X i j) (hW : ∀ i j, (∏ p ∈ P, p) ≤ X i j)
    (hH : ∀ i j, 0 < harmonicNormalizer (X i j) (∏ p ∈ P, p))
    (hlog : ∀ i j, 2 ≤ Real.log (X i j : ℝ))
    (hZ : ∀ i j, powerUnitNormalizer (comparisonExponent (X i j)) 1 ≤ 2 * Real.log (X i j : ℝ))
    (b : ℕ) (hb : ∀ i, Fintype.card (κ i) ≤ b) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hc : ∀ p ∈ S, p.Coprime (∏ p ∈ P, p))
    (D : Finset (MvPolynomial (Fin n) ℤ)) :
    Summable (fun k => (variableHarmonicRowDivisorPMF X (∏ p ∈ P, p) hH k).toReal *
      comparisonPrimePowerCRTIntegrand S hS D k) := by
  apply DiscreteProduct.weighted_summable_of_domination _ _ _ (by positivity)
    (variableHarmonicRowDivisorPMF_atom_domination X P hP hX hW hH hlog hZ)
    _ (fun k => by rw [comparisonPrimePowerCRTIntegrand_eq]; exact comparisonPrimeExcessIntegrand_nonneg S hS D k)
  exact variableComparisonCRT_excess_summable (fun i j => comparisonExponent (X i j))
    (fun i j => comparisonExponent_gt_one (hX i j)) (∏ p ∈ P, p) b hb S hS hc D

theorem variableHarmonicRow_CRT_excess_expectation_bound {q n : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (X : ∀ i, κ i → ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hX : ∀ i j, 2 ≤ X i j) (hW : ∀ i j, (∏ p ∈ P, p) ≤ X i j)
    (hH : ∀ i j, 0 < harmonicNormalizer (X i j) (∏ p ∈ P, p))
    (hlog : ∀ i j, 2 ≤ Real.log (X i j : ℝ))
    (hZ : ∀ i j, powerUnitNormalizer (comparisonExponent (X i j)) 1 ≤ 2 * Real.log (X i j : ℝ))
    (b w : ℕ) (hb : ∀ i, Fintype.card (κ i) ≤ b) (hw : 0 < w)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hc : ∀ p ∈ S, p.Coprime (∏ p ∈ P, p))
    (hgreater : ∀ p ∈ S, w < p) (D : Finset (MvPolynomial (Fin n) ℤ))
    (hD : ∀ f ∈ D, f ≠ 0) (hcut : D.sup integerPolynomialCoeffSize ≤ w)
    (hsmall : localExcessPrimeTestConstant b q D ≤ (w : ℝ)) :
    DiscreteProduct.expectation (variableHarmonicRowDivisorPMF X (∏ p ∈ P, p) hH)
        (comparisonPrimePowerCRTIntegrand S hS D) ≤
      (4 * Real.exp 3) ^ (∑ i, Fintype.card (κ i)) * (2 * localExcessPrimeTestConstant b q D / (w : ℝ)) := by
  have hdom := DiscreteProduct.expectation_le_of_domination
    (variableHarmonicRowDivisorPMF X (∏ p ∈ P, p) hH)
    (variableComparisonRowPMF (fun i j => comparisonExponent (X i j))
      (fun i j => comparisonExponent_gt_one (hX i j)) (∏ p ∈ P, p))
    ((4 * Real.exp 3) ^ (∑ i, Fintype.card (κ i))) (by positivity)
    (variableHarmonicRowDivisorPMF_atom_domination X P hP hX hW hH hlog hZ)
    (comparisonPrimePowerCRTIntegrand S hS D)
    (fun k => by rw [comparisonPrimePowerCRTIntegrand_eq]; exact comparisonPrimeExcessIntegrand_nonneg S hS D k)
    (variableComparisonCRT_excess_summable (fun i j => comparisonExponent (X i j))
      (fun i j => comparisonExponent_gt_one (hX i j)) (∏ p ∈ P, p) b hb S hS hc D)
  exact hdom.trans (mul_le_mul_of_nonneg_left
    (variableComparisonCRT_excess_expectation_tail (fun i j => comparisonExponent (X i j))
      (fun i j => comparisonExponent_gt_one (hX i j)) (∏ p ∈ P, p) b w hb hw S hS hc hgreater D hD hcut hsmall).2
    (by positivity))

end Hindman168
