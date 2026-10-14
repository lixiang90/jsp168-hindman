import Hindman168.CountableExpectations
import Hindman168.LocalExcessPrimeTestMoment
import Hindman168.UnitCRTJointLaw

/-!
# The actual full comparison-law excess expectation

The original row divisors are drawn from their countable comparison law.
The original unit parameters have the proved independent local unit law.
The finite-prime valuation pushforward and the genuine countable product
expectation theorem identify the joint excess expectation with the product
of the actual local means. Its integrand is summable, and the resulting
bound is uniform in the tested finite prime set.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def primeUnitBetaMean {q n : ℕ} (p : ℕ) [NeZero p]
    (D : Finset (MvPolynomial (Fin n) ℤ)) (a : Fin q → ℕ) : ℝ :=
  FiniteMass.expectation (FiniteMass.piMass (fun _ : Fin n => zmodUnitUniformMass p))
    (fun x => localExcessBeta p a (unitPolynomialTestEvent D p x))

theorem primeUnitBetaMean_nonneg {q n : ℕ} (p : ℕ) [NeZero p]
    (D : Finset (MvPolynomial (Fin n) ℤ)) (a : Fin q → ℕ) :
    0 ≤ primeUnitBetaMean p D a :=
  FiniteMass.expectation_nonneg _ _
    (FiniteMass.piMass_nonneg _ (fun _ => zmodUnitUniformMass_nonneg p))
    (fun _ => localExcessBeta_nonneg p a _)

theorem primeUnitBetaMean_summable {q n : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W p : ℕ) [NeZero p]
    (hp : p.Prime) (hc : p.Coprime W) (D : Finset (MvPolynomial (Fin n) ℤ)) :
    Summable (fun a => (DiscreteProduct.piPMF
      (fun i => valuationSumPMF (s i) (hs i) p hp.two_le) a).toReal * primeUnitBetaMean p D a) := by
  rw [← comparisonRowPMF_valuation s hs W p hp hc]
  exact localExcessPrimeTestMoment_integrand_summable s hs W p hp hc D

theorem primeUnitBetaMean_expectation {q n : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W p : ℕ) [NeZero p]
    (hp : p.Prime) (hc : p.Coprime W) (D : Finset (MvPolynomial (Fin n) ℤ)) :
    DiscreteProduct.expectation (DiscreteProduct.piPMF
      (fun i => valuationSumPMF (s i) (hs i) p hp.two_le)) (primeUnitBetaMean p D) =
      localExcessPrimeMean s hs W p D := by
  rw [← comparisonRowPMF_valuation s hs W p hp hc, localExcessPrimeMean_eq s hs W p hp D]
  rfl

theorem primeUnitBetaProduct_expectation {ι : Type*} [Fintype ι] {q n : ℕ}
    (p : ι → ℕ) [∀ i, NeZero (p i)] (D : Finset (MvPolynomial (Fin n) ℤ))
    (a : ι → Fin q → ℕ) :
    FiniteMass.expectation
        (FiniteMass.piMass (fun i => FiniteMass.piMass (fun _ : Fin n => zmodUnitUniformMass (p i))))
        (fun x => (∏ i, (1 + localExcessBeta (p i) (a i) (unitPolynomialTestEvent D (p i) (x i)))) - 1) =
      (∏ i, (1 + primeUnitBetaMean (p i) D (a i))) - 1 := by
  exact FiniteMass.expectation_piMass_product_excess
    (fun i => FiniteMass.piMass (fun _ : Fin n => zmodUnitUniformMass (p i)))
    (fun i => FiniteMass.piMass_total_one _ (fun _ => zmodUnitUniformMass_total (p i)))
    (fun i x => localExcessBeta (p i) (a i) (unitPolynomialTestEvent D (p i) x))

noncomputable def comparisonPrimeExcessIntegrand {q n : ℕ} (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (D : Finset (MvPolynomial (Fin n) ℤ)) (d : Fin q → ℕ) : ℝ := by
  letI : ∀ p : S, NeZero (p : ℕ) := fun p => ⟨(hS p p.property).ne_zero⟩
  exact FiniteMass.expectation
    (FiniteMass.piMass (fun p : S => FiniteMass.piMass (fun _ : Fin n => zmodUnitUniformMass (p : ℕ))))
    (fun x => (∏ p : S, (1 + localExcessBeta (p : ℕ) (fun i => (d i).factorization p)
      (unitPolynomialTestEvent D p (x p)))) - 1)

noncomputable def comparisonPrimeExcessMoment {q n : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (D : Finset (MvPolynomial (Fin n) ℤ)) : ℝ :=
  DiscreteProduct.expectation (comparisonRowPMF s hs W) (comparisonPrimeExcessIntegrand S hS D)

theorem comparisonPrimeExcessIntegrand_eq {q n : ℕ} (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (D : Finset (MvPolynomial (Fin n) ℤ)) (d : Fin q → ℕ) :
    comparisonPrimeExcessIntegrand S hS D d =
      letI : ∀ p : S, NeZero (p : ℕ) := fun p => ⟨(hS p p.property).ne_zero⟩
      (∏ p : S, (1 + primeUnitBetaMean (p : ℕ) D (fun i => (d i).factorization p))) - 1 := by
  letI : ∀ p : S, NeZero (p : ℕ) := fun p => ⟨(hS p p.property).ne_zero⟩
  exact primeUnitBetaProduct_expectation (fun p : S => (p : ℕ)) D _

theorem comparisonPrimeExcessIntegrand_nonneg {q n : ℕ} (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (D : Finset (MvPolynomial (Fin n) ℤ)) (d : Fin q → ℕ) :
    0 ≤ comparisonPrimeExcessIntegrand S hS D d := by
  letI : ∀ p : S, NeZero (p : ℕ) := fun p => ⟨(hS p p.property).ne_zero⟩
  rw [comparisonPrimeExcessIntegrand_eq]
  have h := Finset.one_le_prod (s := (Finset.univ : Finset S))
    (fun (p : S) _ => show 1 ≤ 1 + primeUnitBetaMean (p : ℕ) D (fun i => (d i).factorization p) from
      by linarith [primeUnitBetaMean_nonneg (p : ℕ) D (fun i => (d i).factorization p)])
  linarith

theorem comparisonPrimeExcessIntegrand_summable {q n : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hc : ∀ p ∈ S, p.Coprime W)
    (D : Finset (MvPolynomial (Fin n) ℤ)) :
    Summable (fun d => (comparisonRowPMF s hs W d).toReal * comparisonPrimeExcessIntegrand S hS D d) := by
  letI : ∀ p : S, NeZero (p : ℕ) := fun p => ⟨(hS p p.property).ne_zero⟩
  let μ := fun p : S => DiscreteProduct.piPMF
    (fun i => valuationSumPMF (s i) (hs i) p (hS p p.property).two_le)
  let f : S → (Fin q → ℕ) → ℝ := fun p => primeUnitBetaMean (p : ℕ) D
  let g := fun a : S → Fin q → ℕ => (∏ p : S, (1 + f p (a p))) - 1
  have hg : ∀ a, 0 ≤ g a := by
    intro a
    have h := Finset.one_le_prod (s := (Finset.univ : Finset S))
      (fun p _ => show 1 ≤ 1 + f p (a p) from by linarith [primeUnitBetaMean_nonneg (p : ℕ) D (a p)])
    exact sub_nonneg.mpr h
  have hsum := DiscreteProduct.piPMF_product_excess_summable μ f
    (fun p a => primeUnitBetaMean_nonneg (p : ℕ) D a)
    (fun p => primeUnitBetaMean_summable s hs W p (hS p p.property) (hc p p.property) D)
  have hmap := comparisonRowPMF_prime_columns s hs W S hS hc
  have htarget : Summable (fun a => (((comparisonRowPMF s hs W).map
      (fun d (p : S) i => (d i).factorization p)) a).toReal * g a) := by
    rw [hmap]
    exact hsum
  have hsource := DiscreteProduct.weighted_summable_map_pullback (comparisonRowPMF s hs W)
    (fun d (p : S) i => (d i).factorization p) g hg htarget
  apply hsource.congr
  intro d
  rw [comparisonPrimeExcessIntegrand_eq]

theorem comparisonPrimeExcessMoment_eq {q n : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hc : ∀ p ∈ S, p.Coprime W)
    (D : Finset (MvPolynomial (Fin n) ℤ)) :
    comparisonPrimeExcessMoment s hs W S hS D =
      (∏ p ∈ S, (1 + localExcessPrimeMean s hs W p D)) - 1 := by
  letI : ∀ p : S, NeZero (p : ℕ) := fun p => ⟨(hS p p.property).ne_zero⟩
  let μ := fun p : S => DiscreteProduct.piPMF
    (fun i => valuationSumPMF (s i) (hs i) p (hS p p.property).two_le)
  let f : S → (Fin q → ℕ) → ℝ := fun p => primeUnitBetaMean (p : ℕ) D
  let g := fun a : S → Fin q → ℕ => (∏ p : S, (1 + f p (a p))) - 1
  have hg : ∀ a, 0 ≤ g a := by
    intro a
    have h := Finset.one_le_prod (s := (Finset.univ : Finset S))
      (fun p _ => show 1 ≤ 1 + f p (a p) from by linarith [primeUnitBetaMean_nonneg (p : ℕ) D (a p)])
    exact sub_nonneg.mpr h
  have hmap := comparisonRowPMF_prime_columns s hs W S hS hc
  have h := DiscreteProduct.expectation_map (comparisonRowPMF s hs W)
    (fun d (p : S) i => (d i).factorization p) g hg
  rw [hmap, DiscreteProduct.piPMF_expectation_product_excess μ f
    (fun p a => primeUnitBetaMean_nonneg (p : ℕ) D a)
    (fun p => primeUnitBetaMean_summable s hs W p (hS p p.property) (hc p p.property) D)] at h
  have hlocal (p : S) : DiscreteProduct.expectation (μ p) (f p) =
      localExcessPrimeMean s hs W p D :=
    primeUnitBetaMean_expectation s hs W p (hS p p.property) (hc p p.property) D
  simp only [hlocal] at h
  rw [Finset.prod_coe_sort S (fun p => 1 + localExcessPrimeMean s hs W p D)] at h
  rw [h]
  unfold comparisonPrimeExcessMoment
  congr 1
  funext d
  exact comparisonPrimeExcessIntegrand_eq S hS D d

theorem comparisonPrimeExcessMoment_tail {q n : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W w : ℕ) (hw : 0 < w)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hc : ∀ p ∈ S, p.Coprime W)
    (hgreater : ∀ p ∈ S, w < p) (D : Finset (MvPolynomial (Fin n) ℤ))
    (hD : ∀ f ∈ D, f ≠ 0) (hcut : D.sup integerPolynomialCoeffSize ≤ w)
    (hsmall : localExcessPrimeTestConstant (Fintype.card κ) q D ≤ (w : ℝ)) :
    0 ≤ comparisonPrimeExcessMoment s hs W S hS D ∧
      comparisonPrimeExcessMoment s hs W S hS D ≤
        2 * localExcessPrimeTestConstant (Fintype.card κ) q D / (w : ℝ) := by
  rw [comparisonPrimeExcessMoment_eq s hs W S hS hc D]
  exact actual_local_prime_means_product_tail s hs W w hw S hS hc hgreater D hD hcut hsmall

end Hindman168
