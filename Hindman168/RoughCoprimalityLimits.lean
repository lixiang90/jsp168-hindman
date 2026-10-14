import Hindman168.ConditionalRoughCoprimality
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Vanishing rough-coprimality exceptions along growing actual pools

The common endpoint 2^w is available whenever each coordinate pool's
lower dyadic exponent is at least w. The proved quantitative estimates
then give vanishing probabilities for both actual bad events. Separate
tuple conditioning preserves those limits when its event masses tend to
one; no conditional probability is replaced by an unnormalized mass.
-/

namespace Hindman168.FiniteMass

open Filter
open scoped Topology Classical

theorem event_tensor_conditionMass_tendsto_zero {α β : Type*}
    (μ : ℕ → Mass α) (ν : ℕ → Mass β)
    (A : ℕ → α → Prop) (C : ℕ → β → Prop) (B : ℕ → α × β → Prop)
    (hμ : ∀ w x, 0 ≤ μ w x) (hν : ∀ w y, 0 ≤ ν w y)
    (hA : Tendsto (fun w => event (μ w) (A w)) atTop (𝓝 1))
    (hC : Tendsto (fun w => event (ν w) (C w)) atTop (𝓝 1))
    (hB : Tendsto (fun w => event (tensor (μ w) (ν w)) (B w)) atTop (𝓝 0)) :
    Tendsto (fun w => event (tensor (conditionMass (μ w) (A w)) (conditionMass (ν w) (C w)))
      (B w)) atTop (𝓝 0) := by
  have hAh := hA.eventually (eventually_gt_nhds (by norm_num : (1 : ℝ) / 2 < 1))
  have hCh := hC.eventually (eventually_gt_nhds (by norm_num : (1 : ℝ) / 2 < 1))
  apply squeeze_zero'
  · exact Eventually.of_forall (fun w => event_nonneg _ _
      (tensor_nonneg _ _ (conditionMass_nonneg (μ w) (A w) (hμ w))
        (conditionMass_nonneg (ν w) (C w) (hν w))))
  · filter_upwards [hAh, hCh] with w hwA hwC
    exact event_tensor_conditionMass_half_le (μ w) (ν w) (A w) (C w) (B w)
      (hμ w) (hν w) hwA.le hwC.le
  · simpa only [mul_zero] using hB.const_mul (4 : ℝ)

end Hindman168.FiniteMass

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

theorem dyadic_polynomial_zero_error_tendsto_zero :
    Tendsto (fun w : ℕ => Real.log (2 ^ w : ℕ) / (2 ^ w : ℕ)) atTop (𝓝 0) := by
  have h : Tendsto (fun w : ℕ => ((2 ^ w : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp dyadic_atTop
  exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp h

theorem dyadicCoprimeError_tendsto_zero :
    Tendsto (fun w : ℕ => dyadicCoprimeError w (2 ^ w)) atTop (𝓝 0) := by
  have h : Tendsto (fun w : ℕ => ((2 ^ w : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp dyadic_atTop
  have hs : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  simpa only [dyadicCoprimeError, zero_add, Function.comp_def] using
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).add (hs.comp h)

theorem dyadicPool_bad_events_tendsto_zero {m n : ℕ}
    {F : MvPolynomial (Fin m) ℤ} {G : MvPolynomial (Fin n) ℤ}
    (hF : F ≠ 0) (hG : G ≠ 0)
    (PF : ℕ → Fin m → DyadicPrimePool) (PG : ℕ → Fin n → DyadicPrimePool)
    (hPF : ∀ w i, w ≤ (PF w i).lowerExponent) (hPG : ∀ w i, w ≤ (PG w i).lowerExponent) :
    Tendsto (fun w => event (tensor (dyadicPoolTupleMass (PF w)) (dyadicPoolTupleMass (PG w)))
      (polynomialProductZeroEvent F G)) atTop (𝓝 0) ∧
    Tendsto (fun w => event (tensor (dyadicPoolTupleMass (PF w)) (dyadicPoolTupleMass (PG w)))
      (roughPolynomialGcdEvent w F G)) atTop (𝓝 0) := by
  obtain ⟨w0, e0, K, hk⟩ := exists_dyadicPool_rough_coprimality_bounds hF hG
  have hpow : Tendsto (fun w : ℕ => ((2 ^ w : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp dyadic_atTop
  have hb : ∀ᶠ w in atTop,
      event (tensor (dyadicPoolTupleMass (PF w)) (dyadicPoolTupleMass (PG w)))
        (polynomialProductZeroEvent F G) ≤ (K : ℝ) * (Real.log (2 ^ w : ℕ) / (2 ^ w : ℕ)) ∧
      event (tensor (dyadicPoolTupleMass (PF w)) (dyadicPoolTupleMass (PG w)))
        (roughPolynomialGcdEvent w F G) ≤ (K : ℝ) * dyadicCoprimeError w (2 ^ w) := by
    filter_upwards [eventually_ge_atTop w0, eventually_ge_atTop e0,
      eventually_ge_atTop 1, hpow.eventually (eventually_ge_atTop (Real.exp 2))] with w hw0 he0 hw hL
    exact hk (PF w) (PG w) (fun i => he0.trans (hPF w i)) (fun i => he0.trans (hPG w i))
      w (2 ^ w) hw0 (by omega) hL
      (fun i => Nat.pow_le_pow_right (by decide : 0 < 2) (hPF w i))
      (fun i => Nat.pow_le_pow_right (by decide : 0 < 2) (hPG w i))
  constructor
  · apply squeeze_zero' (Eventually.of_forall (fun w => event_nonneg _ _
      (tensor_nonneg _ _ (dyadicPoolTupleMass_nonneg (PF w)) (dyadicPoolTupleMass_nonneg (PG w)))))
      (hb.mono (fun _ h => h.1))
    simpa only [mul_zero] using dyadic_polynomial_zero_error_tendsto_zero.const_mul (K : ℝ)
  · apply squeeze_zero' (Eventually.of_forall (fun w => event_nonneg _ _
      (tensor_nonneg _ _ (dyadicPoolTupleMass_nonneg (PF w)) (dyadicPoolTupleMass_nonneg (PG w)))))
      (hb.mono (fun _ h => h.2))
    simpa only [mul_zero] using dyadicCoprimeError_tendsto_zero.const_mul (K : ℝ)

theorem conditioned_dyadicPool_bad_events_tendsto_zero {m n : ℕ}
    {F : MvPolynomial (Fin m) ℤ} {G : MvPolynomial (Fin n) ℤ}
    (hF : F ≠ 0) (hG : G ≠ 0)
    (PF : ℕ → Fin m → DyadicPrimePool) (PG : ℕ → Fin n → DyadicPrimePool)
    (hPF : ∀ w i, w ≤ (PF w i).lowerExponent) (hPG : ∀ w i, w ≤ (PG w i).lowerExponent)
    (A : ℕ → (Fin m → ℕ) → Prop) (C : ℕ → (Fin n → ℕ) → Prop)
    (hA : Tendsto (fun w => event (dyadicPoolTupleMass (PF w)) (A w)) atTop (𝓝 1))
    (hC : Tendsto (fun w => event (dyadicPoolTupleMass (PG w)) (C w)) atTop (𝓝 1)) :
    Tendsto (fun w => event
      (tensor (conditionMass (dyadicPoolTupleMass (PF w)) (A w)) (conditionMass (dyadicPoolTupleMass (PG w)) (C w)))
      (polynomialProductZeroEvent F G)) atTop (𝓝 0) ∧
    Tendsto (fun w => event
      (tensor (conditionMass (dyadicPoolTupleMass (PF w)) (A w)) (conditionMass (dyadicPoolTupleMass (PG w)) (C w)))
      (roughPolynomialGcdEvent w F G)) atTop (𝓝 0) := by
  obtain ⟨hz, hg⟩ := dyadicPool_bad_events_tendsto_zero hF hG PF PG hPF hPG
  exact ⟨event_tensor_conditionMass_tendsto_zero _ _ A C _
      (fun w => dyadicPoolTupleMass_nonneg (PF w)) (fun w => dyadicPoolTupleMass_nonneg (PG w)) hA hC hz,
    event_tensor_conditionMass_tendsto_zero _ _ A C _
      (fun w => dyadicPoolTupleMass_nonneg (PF w)) (fun w => dyadicPoolTupleMass_nonneg (PG w)) hA hC hg⟩

end Hindman168
