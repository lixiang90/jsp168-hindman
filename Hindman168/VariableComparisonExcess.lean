import Hindman168.VariableComparisonRows
import Hindman168.ValuationLawMoments
import Hindman168.PrimePowerUnitExcess

/-!
# Actual global excess for different row arities

The variable row valuation columns have their original sum-geometric
laws. The actual local moments follow from the proved common cardinality
atom bound. Prime-column independence identifies the genuine global
expectation with the product of these local means and bounds its tail.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable abbrev variablePrimeValuationPMF {q : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (s : ∀ i, κ i → ℝ) (hs : ∀ i j, 1 < s i j)
    (p : ℕ) (hp : p.Prime) : PMF (Fin q → ℕ) :=
  DiscreteProduct.piPMF (fun i => valuationSumPMF (s i) (hs i) p hp.two_le)

theorem variablePrimeValuationPMF_atom_bound {q : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (s : ∀ i, κ i → ℝ) (hs : ∀ i j, 1 < s i j)
    (p b : ℕ) (hp : p.Prime) (hb : ∀ i, Fintype.card (κ i) ≤ b) (a : Fin q → ℕ) :
    (variablePrimeValuationPMF s hs p hp a).toReal ≤ rowValuationWeight p b a := by
  have h := variableComparisonRowPMF_valuation_atom_bound s hs 1 p b hp (by simp) hb a
  rwa [variableComparisonRowPMF_valuation s hs 1 p hp (by simp)] at h

theorem variablePrimeUnitBeta_summable {q n : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (s : ∀ i, κ i → ℝ) (hs : ∀ i j, 1 < s i j)
    (p b : ℕ) [NeZero p] (hp : p.Prime) (hb : ∀ i, Fintype.card (κ i) ≤ b)
    (D : Finset (MvPolynomial (Fin n) ℤ)) :
    Summable (fun a => (variablePrimeValuationPMF s hs p hp a).toReal * primeUnitBetaMean p D a) :=
  valuationLaw_primeUnitBeta_summable _ p b hp.two_le (variablePrimeValuationPMF_atom_bound s hs p b hp hb) D

noncomputable def variableLocalPrimeMean {q n : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (s : ∀ i, κ i → ℝ) (hs : ∀ i j, 1 < s i j)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (p : ℕ) : ℝ :=
  if hp : p.Prime then
    letI : NeZero p := ⟨hp.ne_zero⟩
    DiscreteProduct.expectation (variablePrimeValuationPMF s hs p hp) (primeUnitBetaMean p D)
  else 0

theorem variableLocalPrimeMean_eq {q n : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (s : ∀ i, κ i → ℝ) (hs : ∀ i j, 1 < s i j)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (p : ℕ) [NeZero p] (hp : p.Prime) :
    variableLocalPrimeMean s hs D p =
      DiscreteProduct.expectation (variablePrimeValuationPMF s hs p hp) (primeUnitBetaMean p D) := by
  simp only [variableLocalPrimeMean, dif_pos hp]

theorem variableLocalPrimeMean_nonneg {q n : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (s : ∀ i, κ i → ℝ) (hs : ∀ i j, 1 < s i j)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (p : ℕ) : 0 ≤ variableLocalPrimeMean s hs D p := by
  by_cases hp : p.Prime
  · letI : NeZero p := ⟨hp.ne_zero⟩
    rw [variableLocalPrimeMean_eq s hs D p hp]
    exact tsum_nonneg (fun a => mul_nonneg ENNReal.toReal_nonneg (primeUnitBetaMean_nonneg p D a))
  · simp only [variableLocalPrimeMean, dif_neg hp, le_refl]

theorem variableLocalPrimeMean_bound {q n : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (s : ∀ i, κ i → ℝ) (hs : ∀ i j, 1 < s i j)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (p b : ℕ) (hp : p.Prime)
    (hb : ∀ i, Fintype.card (κ i) ≤ b) (hD : ∀ f ∈ D, f ≠ 0)
    (hcut : D.sup integerPolynomialCoeffSize < p) :
    variableLocalPrimeMean s hs D p ≤ localExcessPrimeTestConstant b q D / (p : ℝ) ^ 2 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [variableLocalPrimeMean_eq s hs D p hp]
  exact valuationLaw_primeUnitBeta_expectation_bound _ p b hp
    (variablePrimeValuationPMF_atom_bound s hs p b hp hb) D hD hcut

theorem variableLocalPrimeMean_product_tail {q n : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (s : ∀ i, κ i → ℝ) (hs : ∀ i j, 1 < s i j)
    (b w : ℕ) (hb : ∀ i, Fintype.card (κ i) ≤ b) (hw : 0 < w)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hgreater : ∀ p ∈ S, w < p)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    (hcut : D.sup integerPolynomialCoeffSize ≤ w) (hsmall : localExcessPrimeTestConstant b q D ≤ (w : ℝ)) :
    0 ≤ (∏ p ∈ S, (1 + variableLocalPrimeMean s hs D p)) - 1 ∧
      (∏ p ∈ S, (1 + variableLocalPrimeMean s hs D p)) - 1 ≤ 2 * localExcessPrimeTestConstant b q D / (w : ℝ) := by
  apply bounded_local_means_product_excess_le hw S hgreater (variableLocalPrimeMean s hs D)
    (fun p _ => variableLocalPrimeMean_nonneg s hs D p) _ (localExcessPrimeTestConstant_nonneg b q D) hsmall
  intro p hp
  simpa only [div_eq_mul_inv] using variableLocalPrimeMean_bound s hs D p b (hS p hp) hb hD
    (hcut.trans_lt (hgreater p hp))

theorem variableComparisonPrimeExcess_summable {q n : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (s : ∀ i, κ i → ℝ) (hs : ∀ i j, 1 < s i j)
    (W b : ℕ) (hb : ∀ i, Fintype.card (κ i) ≤ b) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hc : ∀ p ∈ S, p.Coprime W)
    (D : Finset (MvPolynomial (Fin n) ℤ)) :
    Summable (fun k => (variableComparisonRowPMF s hs W k).toReal * comparisonPrimeExcessIntegrand S hS D k) := by
  letI : ∀ p : S, NeZero (p : ℕ) := fun p => ⟨(hS p p.property).ne_zero⟩
  let μ := fun p : S => variablePrimeValuationPMF s hs p (hS p p.property)
  let f : S → (Fin q → ℕ) → ℝ := fun p => primeUnitBetaMean (p : ℕ) D
  let g := fun a : S → Fin q → ℕ => (∏ p : S, (1 + f p (a p))) - 1
  have hg : ∀ a, 0 ≤ g a := by
    intro a
    exact sub_nonneg.mpr (Finset.one_le_prod (fun p _ => by linarith [primeUnitBetaMean_nonneg (p : ℕ) D (a p)]))
  have hsum := DiscreteProduct.piPMF_product_excess_summable μ f
    (fun p a => primeUnitBetaMean_nonneg (p : ℕ) D a)
    (fun p => variablePrimeUnitBeta_summable s hs p b (hS p p.property) hb D)
  have hmap := variableComparisonRowPMF_prime_columns s hs W S hS hc
  have htarget : Summable (fun a => (((variableComparisonRowPMF s hs W).map
      (fun k (p : S) i => (k i).factorization p)) a).toReal * g a) := by rw [hmap]; exact hsum
  have hsource := DiscreteProduct.weighted_summable_map_pullback (variableComparisonRowPMF s hs W)
    (fun k (p : S) i => (k i).factorization p) g hg htarget
  apply hsource.congr
  intro k
  rw [comparisonPrimeExcessIntegrand_eq]

theorem variableComparisonPrimeExcess_expectation_eq {q n : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (s : ∀ i, κ i → ℝ) (hs : ∀ i j, 1 < s i j)
    (W b : ℕ) (hb : ∀ i, Fintype.card (κ i) ≤ b) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hc : ∀ p ∈ S, p.Coprime W)
    (D : Finset (MvPolynomial (Fin n) ℤ)) :
    DiscreteProduct.expectation (variableComparisonRowPMF s hs W) (comparisonPrimeExcessIntegrand S hS D) =
      (∏ p ∈ S, (1 + variableLocalPrimeMean s hs D p)) - 1 := by
  letI : ∀ p : S, NeZero (p : ℕ) := fun p => ⟨(hS p p.property).ne_zero⟩
  let μ := fun p : S => variablePrimeValuationPMF s hs p (hS p p.property)
  let f : S → (Fin q → ℕ) → ℝ := fun p => primeUnitBetaMean (p : ℕ) D
  let g := fun a : S → Fin q → ℕ => (∏ p : S, (1 + f p (a p))) - 1
  have hg : ∀ a, 0 ≤ g a := by
    intro a
    exact sub_nonneg.mpr (Finset.one_le_prod (fun p _ => by linarith [primeUnitBetaMean_nonneg (p : ℕ) D (a p)]))
  have h := DiscreteProduct.expectation_map (variableComparisonRowPMF s hs W)
    (fun k (p : S) i => (k i).factorization p) g hg
  rw [variableComparisonRowPMF_prime_columns s hs W S hS hc,
    DiscreteProduct.piPMF_expectation_product_excess μ f
      (fun p a => primeUnitBetaMean_nonneg (p : ℕ) D a)
      (fun p => variablePrimeUnitBeta_summable s hs p b (hS p p.property) hb D)] at h
  have hlocal (p : S) : DiscreteProduct.expectation (μ p) (f p) = variableLocalPrimeMean s hs D p :=
    (variableLocalPrimeMean_eq s hs D p (hS p p.property)).symm
  simp only [hlocal] at h
  rw [Finset.prod_coe_sort S (fun p => 1 + variableLocalPrimeMean s hs D p)] at h
  rw [h]
  congr 1
  funext k
  exact comparisonPrimeExcessIntegrand_eq S hS D k

theorem variableComparisonCRT_excess_summable {q n : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (s : ∀ i, κ i → ℝ) (hs : ∀ i j, 1 < s i j)
    (W b : ℕ) (hb : ∀ i, Fintype.card (κ i) ≤ b) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hc : ∀ p ∈ S, p.Coprime W)
    (D : Finset (MvPolynomial (Fin n) ℤ)) :
    Summable (fun k => (variableComparisonRowPMF s hs W k).toReal * comparisonPrimePowerCRTIntegrand S hS D k) := by
  simp only [comparisonPrimePowerCRTIntegrand_eq]
  exact variableComparisonPrimeExcess_summable s hs W b hb S hS hc D

theorem variableComparisonCRT_excess_expectation_tail {q n : ℕ} {κ : Fin q → Type*}
    [∀ i, Fintype (κ i)] (s : ∀ i, κ i → ℝ) (hs : ∀ i j, 1 < s i j)
    (W b w : ℕ) (hb : ∀ i, Fintype.card (κ i) ≤ b) (hw : 0 < w)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hc : ∀ p ∈ S, p.Coprime W)
    (hgreater : ∀ p ∈ S, w < p) (D : Finset (MvPolynomial (Fin n) ℤ))
    (hD : ∀ f ∈ D, f ≠ 0) (hcut : D.sup integerPolynomialCoeffSize ≤ w)
    (hsmall : localExcessPrimeTestConstant b q D ≤ (w : ℝ)) :
    0 ≤ DiscreteProduct.expectation (variableComparisonRowPMF s hs W) (comparisonPrimePowerCRTIntegrand S hS D) ∧
      DiscreteProduct.expectation (variableComparisonRowPMF s hs W) (comparisonPrimePowerCRTIntegrand S hS D) ≤
        2 * localExcessPrimeTestConstant b q D / (w : ℝ) := by
  have he : comparisonPrimePowerCRTIntegrand (q := q) S hS D = comparisonPrimeExcessIntegrand S hS D :=
    funext (comparisonPrimePowerCRTIntegrand_eq S hS D)
  rw [he, variableComparisonPrimeExcess_expectation_eq s hs W b hb S hS hc D]
  exact variableLocalPrimeMean_product_tail s hs b w hb hw S hS hgreater D hD hcut hsmall

end Hindman168
