import Hindman168.MasterDivisorSampling

/-!
# Uniform vanishing of the actual master-chain CRT excess

The chain, repeated occurrence labels and finite rough-prime set may all
vary with the master parameter. The expectation is taken under the actual
original finite independent tail-divisor law. The bound is uniform in
these choices and uses only the fixed master index size and test family.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem prime_coprime_primorial_of_gt {p w : ℕ} (hp : p.Prime) (hw : w < p) :
    p.Coprime (primorial w) := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  exact (Nat.not_le_of_lt hw) (hp.dvd_primorial_iff.mp hd)

theorem MasterParameterConditions.chain_divisor_CRT_excess_bound {n N m q r : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (T : Finset (MvPolynomial (Fin r) ℤ))
    (hT : ∀ f ∈ T, f ≠ 0) :
    ∀ᶠ w in atTop, ∀ (C : Chain m), (∀ i, C.block i ⊆ Finset.range N) →
      ∀ (label : Fin q → Fin m) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime),
        (∀ p ∈ S, w < p) →
        0 ≤ expectation (piMass (fun i => tailMass (primorial w)
            (C.tailCutoffs (F.cutoff w) (label i)))) (comparisonPrimePowerCRTIntegrand S hS T) ∧
        expectation (piMass (fun i => tailMass (primorial w)
            (C.tailCutoffs (F.cutoff w) (label i)))) (comparisonPrimePowerCRTIntegrand S hS T) ≤
          (4 * Real.exp 3) ^ (N * q) * (2 * localExcessPrimeTestConstant N q T / (w : ℝ)) := by
  have hsmall : ∀ᶠ w : ℕ in atTop, localExcessPrimeTestConstant N q T ≤ (w : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hF.raw_comparison_cutoffs, eventually_ge_atTop 1,
    eventually_ge_atTop (T.sup integerPolynomialCoeffSize), hsmall]
      with w hv hw hcut hsmallw
  intro C hN label S hS hgreater
  let X : ∀ (i : Fin q), C.tail (label i) → ℕ := fun i j => F.cutoff w j
  have hfields (i : Fin q) (j : C.tail (label i)) :=
    hv j (hN (label i) (Finset.mem_insert_of_mem j.property))
  have heq : (∏ p ∈ Nat.primesLE w, p) = primorial w :=
    (primorial_eq_prod_primesLE w).symm
  have hX : ∀ i j, 2 ≤ X i j := fun i j => (hfields i j).1
  have hW : ∀ i j, (∏ p ∈ Nat.primesLE w, p) ≤ X i j := by
    rw [heq]
    exact fun i j => (hfields i j).2.1
  have hH : ∀ i j, 0 < harmonicNormalizer (X i j) (∏ p ∈ Nat.primesLE w, p) := by
    rw [heq]
    exact fun i j => (hfields i j).2.2.1
  have hlog : ∀ i j, 2 ≤ Real.log (X i j : ℝ) := fun i j => (hfields i j).2.2.2.1
  have hZ : ∀ i j, powerUnitNormalizer (comparisonExponent (X i j)) 1 ≤ 2 * Real.log (X i j : ℝ) :=
    fun i j => (hfields i j).2.2.2.2
  have hc : ∀ p ∈ S, p.Coprime (∏ p ∈ Nat.primesLE w, p) := by
    rw [heq]
    exact fun p hp => prime_coprime_primorial_of_gt (hS p hp) (hgreater p hp)
  have hbound := variableHarmonicRow_CRT_excess_expectation_bound X (Nat.primesLE w)
    (fun p hp => Nat.prime_of_mem_primesLE hp) hX hW hH hlog hZ N w
    (fun i => chain_tail_raw_count_le C hN (label i)) (by omega) S hS hc hgreater T hT hcut hsmallw
  rw [← variableHarmonicRowDivisorMass_expectation X _ hH] at hbound
  have hmass : variableHarmonicRowDivisorMass X (∏ p ∈ Nat.primesLE w, p) =
      piMass (fun i => tailMass (primorial w) (C.tailCutoffs (F.cutoff w) (label i))) := by
    simp only [variableHarmonicRowDivisorMass, X, heq, harmonicDivisorMass_chain_tail]
  have hnonneg : 0 ≤ expectation (variableHarmonicRowDivisorMass X (∏ p ∈ Nat.primesLE w, p))
      (comparisonPrimePowerCRTIntegrand S hS T) := by
    apply expectation_nonneg_support _ _ (variableHarmonicRowDivisorMass_nonneg X _ hH)
    intro k hk
    rw [comparisonPrimePowerCRTIntegrand_eq]
    exact comparisonPrimeExcessIntegrand_nonneg S hS T k
  rw [hmass] at hbound hnonneg
  refine ⟨hnonneg, hbound.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (variable_raw_comparison_cost_le N (fun i => chain_tail_raw_count_le C hN (label i)))
    (div_nonneg (mul_nonneg (by norm_num) (localExcessPrimeTestConstant_nonneg N q T)) (Nat.cast_nonneg w))

theorem MasterParameterConditions.chain_divisor_CRT_excess_tendsto_zero {n N m q r : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (T : Finset (MvPolynomial (Fin r) ℤ))
    (hT : ∀ f ∈ T, f ≠ 0) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin q → Fin m) (S : ℕ → Finset ℕ)
    (hS : ∀ w, ∀ p ∈ S w, p.Prime) (hgreater : ∀ w, ∀ p ∈ S w, w < p) :
    Tendsto (fun w => expectation (piMass (fun i => tailMass (primorial w)
        ((C w).tailCutoffs (F.cutoff w) (label w i))))
      (comparisonPrimePowerCRTIntegrand (S w) (hS w) T)) atTop (𝓝 0) := by
  have hb := (hF.chain_divisor_CRT_excess_bound T hT).mono
    (fun w hw => hw (C w) (hN w) (label w) (S w) (hS w) (hgreater w))
  apply squeeze_zero' (hb.mono (fun _ hw => hw.1)) (hb.mono (fun _ hw => hw.2))
  have hi := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
    tendsto_const_nhds.mul (tendsto_const_nhds.mul hi)

end Hindman168
