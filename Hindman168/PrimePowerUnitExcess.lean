import Hindman168.ComparisonPrimeExcessExpectation

/-!
# Original divisor-dependent prime-power unit sampling

CRT is performed at the original prime-power moduli, including exponent
zero. At a zero exponent every row valuation is zero and beta vanishes;
no invalid projection from ZMod 1 to ZMod p is used. Positive exponents
project to the actual uniform mod-prime unit law. Consequently the full
divisor-dependent CRT expectation is the comparison excess moment.
-/

namespace Hindman168

open scoped BigOperators Classical

def primePowerUnitTest {n : ℕ} (p e : ℕ) [NeZero p]
    (D : Finset (MvPolynomial (Fin n) ℤ)) (x : Fin n → ZMod (p ^ e)) : Prop :=
  if he : e = 0 then False else
    unitPolynomialTestEvent D p (fun j => ZMod.castHom (dvd_pow_self p he) (ZMod p) (x j))

theorem localExcessBeta_zero_of_all_zero {q : ℕ} (p : ℕ) (a : Fin q → ℕ)
    (ha : ∀ i, a i = 0) (bad : Prop) : localExcessBeta p a bad = 0 := by
  apply localExcessBeta_eq_zero_of_few
  simp [positiveRowSet, ha]

theorem primePowerUnitBeta_expectation {q n : ℕ} (p e : ℕ) [NeZero p]
    (D : Finset (MvPolynomial (Fin n) ℤ)) (a : Fin q → ℕ) (ha : ∀ i, a i ≤ e) :
    FiniteMass.expectation (FiniteMass.piMass (fun _ : Fin n => zmodUnitUniformMass (p ^ e)))
        (fun x => localExcessBeta p a (primePowerUnitTest p e D x)) = primeUnitBetaMean p D a := by
  by_cases he : e = 0
  · have hz : ∀ i, a i = 0 := fun i => by have h := ha i; omega
    have hb := localExcessBeta_zero_of_all_zero p a hz
    simp only [primeUnitBetaMean, hb, FiniteMass.expectation, mul_zero, Finsupp.sum_fun_zero]
  · have hmap :
        (FiniteMass.piMass (fun _ : Fin n => zmodUnitUniformMass (p ^ e))).mapDomain
          (fun x j => ZMod.castHom (dvd_pow_self p he) (ZMod p) (x j)) =
        FiniteMass.piMass (fun _ : Fin n => zmodUnitUniformMass p) := by
      rw [FiniteMass.piMass_map (fun _ : Fin n => zmodUnitUniformMass (p ^ e))
        (fun _ => ZMod.castHom (dvd_pow_self p he) (ZMod p))]
      simp only [zmodUnitUniformMass_quotient (dvd_pow_self p he)]
    have h := FiniteMass.expectation_push
      (FiniteMass.piMass (fun _ : Fin n => zmodUnitUniformMass (p ^ e)))
      (fun x j => ZMod.castHom (dvd_pow_self p he) (ZMod p) (x j))
      (fun x => localExcessBeta p a (unitPolynomialTestEvent D p x))
    rw [hmap] at h
    simpa only [primePowerUnitTest, dif_neg he, primeUnitBetaMean] using h.symm

theorem primePowerModuli_pairwise_coprime {ι : Type*} (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) (e : ι → ℕ) :
    Pairwise (fun i j => (p i ^ e i).Coprime (p j ^ e j)) := by
  intro i j hij
  exact Nat.coprime_pow_primes (e i) (e j) (hp i) (hp j) (fun h => hij (hinj h))

noncomputable def primePowerCRTExcessIntegrand {ι : Type*} [Fintype ι] {q n : ℕ}
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) (e : ι → ℕ)
    (a : ι → Fin q → ℕ) (D : Finset (MvPolynomial (Fin n) ℤ)) : ℝ := by
  letI : ∀ i, NeZero (p i) := fun i => ⟨(hp i).ne_zero⟩
  letI : NeZero (∏ i, p i ^ e i) := ⟨Finset.prod_ne_zero_iff.mpr
    (fun i _ => pow_ne_zero (e i) (hp i).ne_zero)⟩
  exact FiniteMass.expectation
    (FiniteMass.piMass (fun _ : Fin n => zmodUnitUniformMass (∏ i, p i ^ e i)))
    (fun x => (∏ i, (1 + localExcessBeta (p i) (a i)
      (primePowerUnitTest (p i) (e i) D
        (fun j => ZMod.prodEquivPi (fun i => p i ^ e i)
          (primePowerModuli_pairwise_coprime p hp hinj e) (x j) i)))) - 1)

theorem primePowerCRTExcessIntegrand_eq {ι : Type*} [Fintype ι] {q n : ℕ}
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) (e : ι → ℕ)
    (a : ι → Fin q → ℕ) (ha : ∀ i u, a i u ≤ e i) (D : Finset (MvPolynomial (Fin n) ℤ)) :
    primePowerCRTExcessIntegrand p hp hinj e a D =
      letI : ∀ i, NeZero (p i) := fun i => ⟨(hp i).ne_zero⟩
      (∏ i, (1 + primeUnitBetaMean (p i) D (a i))) - 1 := by
  letI : ∀ i, NeZero (p i) := fun i => ⟨(hp i).ne_zero⟩
  letI : NeZero (∏ i, p i ^ e i) := ⟨Finset.prod_ne_zero_iff.mpr
    (fun i _ => pow_ne_zero (e i) (hp i).ne_zero)⟩
  let μ := FiniteMass.piMass (fun _ : Fin n => zmodUnitUniformMass (∏ i, p i ^ e i))
  let stat : (Fin n → ZMod (∏ i, p i ^ e i)) → (∀ i, Fin n → ZMod (p i ^ e i)) :=
    fun x i j => ZMod.prodEquivPi (fun i => p i ^ e i)
      (primePowerModuli_pairwise_coprime p hp hinj e) (x j) i
  let f := fun x : ∀ i, Fin n → ZMod (p i ^ e i) =>
    (∏ i, (1 + localExcessBeta (p i) (a i) (primePowerUnitTest (p i) (e i) D (x i)))) - 1
  have hpush := zmodUnitUniformMass_crt_vector (fun i => p i ^ e i)
    (primePowerModuli_pairwise_coprime p hp hinj e) n
  have h := FiniteMass.expectation_push μ stat f
  rw [hpush] at h
  rw [FiniteMass.expectation_piMass_product_excess
    (fun i => FiniteMass.piMass (fun _ : Fin n => zmodUnitUniformMass (p i ^ e i)))
    (fun i => FiniteMass.piMass_total_one _ (fun _ => zmodUnitUniformMass_total (p i ^ e i)))
    (fun i x => localExcessBeta (p i) (a i) (primePowerUnitTest (p i) (e i) D x))] at h
  simp only [primePowerUnitBeta_expectation _ _ D _ (ha _)] at h
  exact h.symm

noncomputable def comparisonPrimePowerCRTIntegrand {q n : ℕ} (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (D : Finset (MvPolynomial (Fin n) ℤ)) (d : Fin q → ℕ) : ℝ :=
  primePowerCRTExcessIntegrand (fun p : S => (p : ℕ)) (fun p => hS p p.property)
    Subtype.val_injective (fun p : S => ∑ i, (d i).factorization p)
      (fun p : S => fun i => (d i).factorization p) D

theorem comparisonPrimePowerCRTIntegrand_eq {q n : ℕ} (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (D : Finset (MvPolynomial (Fin n) ℤ)) (d : Fin q → ℕ) :
    comparisonPrimePowerCRTIntegrand S hS D d = comparisonPrimeExcessIntegrand S hS D d := by
  rw [comparisonPrimePowerCRTIntegrand, primePowerCRTExcessIntegrand_eq
    (fun p : S => (p : ℕ)) (fun p => hS p p.property) Subtype.val_injective
    (fun p : S => ∑ i, (d i).factorization p) (fun p : S => fun i => (d i).factorization p)
    (fun p u => (rowValuation_le_max (fun i => (d i).factorization p) u).trans
      (rowMaxValuation_le_sum (fun i => (d i).factorization p))) D,
    comparisonPrimeExcessIntegrand_eq]

theorem comparisonPrimePowerCRTIntegrand_summable {q n : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hc : ∀ p ∈ S, p.Coprime W)
    (D : Finset (MvPolynomial (Fin n) ℤ)) :
    Summable (fun d => (comparisonRowPMF s hs W d).toReal * comparisonPrimePowerCRTIntegrand S hS D d) := by
  simp only [comparisonPrimePowerCRTIntegrand_eq]
  exact comparisonPrimeExcessIntegrand_summable s hs W S hS hc D

theorem comparisonPrimePowerCRT_expectation_tail {q n : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W w : ℕ) (hw : 0 < w)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hc : ∀ p ∈ S, p.Coprime W)
    (hgreater : ∀ p ∈ S, w < p) (D : Finset (MvPolynomial (Fin n) ℤ))
    (hD : ∀ f ∈ D, f ≠ 0) (hcut : D.sup integerPolynomialCoeffSize ≤ w)
    (hsmall : localExcessPrimeTestConstant (Fintype.card κ) q D ≤ (w : ℝ)) :
    0 ≤ DiscreteProduct.expectation (comparisonRowPMF s hs W) (comparisonPrimePowerCRTIntegrand S hS D) ∧
      DiscreteProduct.expectation (comparisonRowPMF s hs W) (comparisonPrimePowerCRTIntegrand S hS D) ≤
        2 * localExcessPrimeTestConstant (Fintype.card κ) q D / (w : ℝ) := by
  have he : comparisonPrimePowerCRTIntegrand (q := q) S hS D =
      comparisonPrimeExcessIntegrand (q := q) S hS D :=
    funext (comparisonPrimePowerCRTIntegrand_eq (q := q) S hS D)
  rw [he]
  exact comparisonPrimeExcessMoment_tail s hs W w hw S hS hc hgreater D hD hcut hsmall

end Hindman168
