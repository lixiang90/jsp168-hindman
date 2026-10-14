import Hindman168.LocalExcessValuationMoments
import Hindman168.PrimeUnitPolynomialTests
import Hindman168.FiniteProductExpectations
import Hindman168.FiniteExcessTail

/-!
# The actual local prime-test excess moment is O(p^-2)

The valuation variables have the original countable comparison law;
the unit parameters have the original independent finite uniform-unit
law. The moment is an explicit iterated expectation under these laws.
No local moment bound is assumed. The polynomial tests contribute C/p
to the bad branch, and the valuation-cell bounds supply the other 1/p.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem expectation_event_two_values {α : Type*} (μ : Mass α) (E : α → Prop)
    (b g : ℝ) :
    expectation μ (fun x => if E x then b else g) =
      event μ E * b + (total μ - event μ E) * g := by
  classical
  have he (x : α) : μ x * (if E x then b else g) =
      (if E x then μ x else 0) * b + (μ x - (if E x then μ x else 0)) * g := by
    split_ifs <;> ring
  rw [expectation_eq_sum _ _ (Finset.Subset.refl _),
    event_eq_sum _ _ (Finset.Subset.refl _), total_eq_sum _ (Finset.Subset.refl _)]
  simp_rw [he, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib]

end Hindman168.FiniteMass

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem localExcessBeta_event_cases {q : ℕ} (p : ℕ) (a : Fin q → ℕ) (E : Prop) :
    localExcessBeta p a E =
      if E then localExcessBeta p a True else localExcessBeta p a False := by
  classical
  by_cases h : E <;> simp [localExcessBeta, h]

theorem localExcessBeta_unit_expectation {q n : ℕ} (p : ℕ) [NeZero p]
    (a : Fin q → ℕ) (D : Finset (MvPolynomial (Fin n) ℤ)) :
    expectation (piMass (fun _ : Fin n => zmodUnitUniformMass p))
        (fun x => localExcessBeta p a (unitPolynomialTestEvent D p x)) =
      event (piMass (fun _ : Fin n => zmodUnitUniformMass p)) (unitPolynomialTestEvent D p) *
        localExcessBeta p a True +
      (1 - event (piMass (fun _ : Fin n => zmodUnitUniformMass p)) (unitPolynomialTestEvent D p)) *
        localExcessBeta p a False := by
  classical
  have he : (fun x => localExcessBeta p a (unitPolynomialTestEvent D p x)) =
      (fun x => if unitPolynomialTestEvent D p x then localExcessBeta p a True
        else localExcessBeta p a False) :=
    funext (fun x => localExcessBeta_event_cases p a _)
  rw [he, expectation_event_two_values,
    piMass_total_one _ (fun _ => zmodUnitUniformMass_total p)]

noncomputable def localExcessPrimeTestMoment {q n : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W p : ℕ) [NeZero p]
    (D : Finset (MvPolynomial (Fin n) ℤ)) : ℝ :=
  ∑' a, (((comparisonRowPMF s hs W).map
    (fun x i => (x i).factorization p)) a).toReal *
      expectation (piMass (fun _ : Fin n => zmodUnitUniformMass p))
        (fun x => localExcessBeta p a (unitPolynomialTestEvent D p x))

theorem localExcessPrimeTestMoment_integrand_summable {q n : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W p : ℕ) [NeZero p]
    (hp : p.Prime) (hc : p.Coprime W) (D : Finset (MvPolynomial (Fin n) ℤ)) :
    Summable (fun a => (((comparisonRowPMF s hs W).map
      (fun x i => (x i).factorization p)) a).toReal *
        expectation (piMass (fun _ : Fin n => zmodUnitUniformMass p))
          (fun x => localExcessBeta p a (unitPolynomialTestEvent D p x))) := by
  have h := ((comparisonRowPMF_bad_beta_summable s hs W p hp hc).mul_left
      (event (piMass (fun _ : Fin n => zmodUnitUniformMass p)) (unitPolynomialTestEvent D p))).add
    ((comparisonRowPMF_good_beta_summable s hs W p hp hc).mul_left
      (1 - event (piMass (fun _ : Fin n => zmodUnitUniformMass p)) (unitPolynomialTestEvent D p)))
  apply h.congr
  intro a
  rw [localExcessBeta_unit_expectation]
  ring

theorem localExcessPrimeTestMoment_eq {q n : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W p : ℕ) [NeZero p]
    (hp : p.Prime) (hc : p.Coprime W) (D : Finset (MvPolynomial (Fin n) ℤ)) :
    localExcessPrimeTestMoment s hs W p D =
      event (piMass (fun _ : Fin n => zmodUnitUniformMass p)) (unitPolynomialTestEvent D p) *
        (∑' a, (((comparisonRowPMF s hs W).map
          (fun x i => (x i).factorization p)) a).toReal * localExcessBeta p a True) +
      (1 - event (piMass (fun _ : Fin n => zmodUnitUniformMass p)) (unitPolynomialTestEvent D p)) *
        (∑' a, (((comparisonRowPMF s hs W).map
          (fun x i => (x i).factorization p)) a).toReal * localExcessBeta p a False) := by
  classical
  unfold localExcessPrimeTestMoment
  simp_rw [localExcessBeta_unit_expectation]
  have he (m B G δ : ℝ) : m * (δ * B + (1 - δ) * G) =
      δ * (m * B) + (1 - δ) * (m * G) := by ring
  simp_rw [he]
  rw [Summable.tsum_add
    ((comparisonRowPMF_bad_beta_summable s hs W p hp hc).mul_left _)
    ((comparisonRowPMF_good_beta_summable s hs W p hp hc).mul_left _),
    tsum_mul_left, tsum_mul_left]

theorem localExcessPrimeTestMoment_nonneg {q n : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W p : ℕ) [NeZero p]
    (D : Finset (MvPolynomial (Fin n) ℤ)) :
    0 ≤ localExcessPrimeTestMoment s hs W p D := by
  apply tsum_nonneg
  intro a
  exact mul_nonneg ENNReal.toReal_nonneg
    (expectation_nonneg _ _ (piMass_nonneg _ (fun _ => zmodUnitUniformMass_nonneg p))
      (fun x => localExcessBeta_nonneg p a _))

theorem localExcessPrimeTestMoment_bound {q n : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W p : ℕ) [NeZero p]
    (hp : p.Prime) (hc : p.Coprime W) (D : Finset (MvPolynomial (Fin n) ℤ))
    (hD : ∀ f ∈ D, f ≠ 0) (hcut : D.sup integerPolynomialCoeffSize < p) :
    localExcessPrimeTestMoment s hs W p D ≤
      ((2 * (∑ f ∈ D, ∑ i, (f.degreeOf i : ℝ)) +
          (q : ℝ) * polynomialGeometricConstant (Fintype.card κ)) *
        polynomialGeometricConstant ((Fintype.card κ + 1) * q)) / (p : ℝ) ^ 2 := by
  let μ := piMass (fun _ : Fin n => zmodUnitUniformMass p)
  let δ := event μ (unitPolynomialTestEvent D p)
  have hδ : 0 ≤ δ := event_nonneg _ _
    (piMass_nonneg _ (fun _ => zmodUnitUniformMass_nonneg p))
  have hδ1 : δ ≤ 1 := by
    have h := event_le_total μ (unitPolynomialTestEvent D p)
      (piMass_nonneg _ (fun _ => zmodUnitUniformMass_nonneg p))
    simpa only [μ, piMass_total_one _ (fun _ => zmodUnitUniformMass_total p)] using h
  have hb := comparisonRowPMF_bad_beta_tsum_bound s hs W p hp hc
  have hg := comparisonRowPMF_good_beta_tsum_bound s hs W p hp hc
  have hbn : 0 ≤ ∑' a, (((comparisonRowPMF s hs W).map
      (fun x i => (x i).factorization p)) a).toReal * localExcessBeta p a True :=
    tsum_nonneg (fun a => mul_nonneg ENNReal.toReal_nonneg (localExcessBeta_nonneg p a True))
  have hgn : 0 ≤ ∑' a, (((comparisonRowPMF s hs W).map
      (fun x i => (x i).factorization p)) a).toReal * localExcessBeta p a False :=
    tsum_nonneg (fun a => mul_nonneg ENNReal.toReal_nonneg (localExcessBeta_nonneg p a False))
  rw [localExcessPrimeTestMoment_eq s hs W p hp hc D]
  change δ * _ + (1 - δ) * _ ≤ _
  have ht := integerPolynomial_family_prime_unit_uniform_bound hp D hD hcut
  calc
    _ ≤ (2 * (∑ f ∈ D, ∑ i, (f.degreeOf i : ℝ)) / (p : ℝ)) *
        (polynomialGeometricConstant ((Fintype.card κ + 1) * q) / (p : ℝ)) +
        (q : ℝ) * (polynomialGeometricConstant (Fintype.card κ) *
          polynomialGeometricConstant ((Fintype.card κ + 1) * q) / (p : ℝ) ^ 2) := by
      apply add_le_add
      · exact mul_le_mul ht hb hbn (by positivity)
      · exact (mul_le_mul_of_nonneg_right (show 1 - δ ≤ 1 by linarith) hgn).trans
          (by simpa only [one_mul] using hg)
    _ = _ := by
      have hpn : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      field_simp

noncomputable def localExcessPrimeTestConstant {n : ℕ} (b q : ℕ)
    (D : Finset (MvPolynomial (Fin n) ℤ)) : ℝ :=
  (2 * (∑ f ∈ D, ∑ i, (f.degreeOf i : ℝ)) +
    (q : ℝ) * polynomialGeometricConstant b) * polynomialGeometricConstant ((b + 1) * q)

theorem localExcessPrimeTestConstant_nonneg {n : ℕ} (b q : ℕ)
    (D : Finset (MvPolynomial (Fin n) ℤ)) :
    0 ≤ localExcessPrimeTestConstant b q D := by
  unfold localExcessPrimeTestConstant
  have hb := polynomialGeometricConstant_nonneg b
  have hq := polynomialGeometricConstant_nonneg ((b + 1) * q)
  positivity

noncomputable def localExcessPrimeMean {q n : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W p : ℕ)
    (D : Finset (MvPolynomial (Fin n) ℤ)) : ℝ :=
  if hp : p.Prime then
    letI : NeZero p := ⟨hp.ne_zero⟩
    localExcessPrimeTestMoment s hs W p D
  else 0

theorem localExcessPrimeMean_eq {q n : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W p : ℕ) [NeZero p]
    (hp : p.Prime) (D : Finset (MvPolynomial (Fin n) ℤ)) :
    localExcessPrimeMean s hs W p D = localExcessPrimeTestMoment s hs W p D := by
  simp only [localExcessPrimeMean, dif_pos hp]

theorem localExcessPrimeMean_nonneg {q n : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W p : ℕ)
    (D : Finset (MvPolynomial (Fin n) ℤ)) :
    0 ≤ localExcessPrimeMean s hs W p D := by
  by_cases hp : p.Prime
  · haveI : NeZero p := ⟨hp.ne_zero⟩
    rw [localExcessPrimeMean_eq s hs W p hp D]
    exact localExcessPrimeTestMoment_nonneg s hs W p D
  · simp only [localExcessPrimeMean, dif_neg hp, le_refl]

theorem actual_local_prime_means_product_tail {q n : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W w : ℕ)
    (hw : 0 < w) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hc : ∀ p ∈ S, p.Coprime W) (hgreater : ∀ p ∈ S, w < p)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    (hcut : D.sup integerPolynomialCoeffSize ≤ w)
    (hsmall : localExcessPrimeTestConstant (Fintype.card κ) q D ≤ (w : ℝ)) :
    0 ≤ (∏ p ∈ S, (1 + localExcessPrimeMean s hs W p D)) - 1 ∧
      (∏ p ∈ S, (1 + localExcessPrimeMean s hs W p D)) - 1 ≤
        2 * localExcessPrimeTestConstant (Fintype.card κ) q D / (w : ℝ) := by
  apply bounded_local_means_product_excess_le hw S hgreater
    (fun p => localExcessPrimeMean s hs W p D)
    (fun p _ => localExcessPrimeMean_nonneg s hs W p D)
    _ (localExcessPrimeTestConstant_nonneg _ _ D) hsmall
  intro p hpS
  haveI : NeZero p := ⟨(hS p hpS).ne_zero⟩
  rw [localExcessPrimeMean_eq s hs W p (hS p hpS) D]
  simpa only [localExcessPrimeTestConstant, div_eq_mul_inv] using
    localExcessPrimeTestMoment_bound s hs W p (hS p hpS) (hc p hpS) D hD
      (hcut.trans_lt (hgreater p hpS))

end Hindman168
