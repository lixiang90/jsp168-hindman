import Hindman168.MasterParameterFamily
import Hindman168.PrimeGoodSamples
import Hindman168.FiniteReplicaConditioning

/-!
# Actual retained prime tuples: nonzero, distinct, no small-prime exception

All three exclusions use the original reciprocal-prime probability law.
The master conditions derive probability tending to one. This is stronger
than merely nonzero polynomial values and supplies the actual conditioning
denominator for replicas whose polynomial family is the master's family.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

def masterPredictionPrimeGoodEvent {n : ℕ} (F : MasterParameterFamily)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (w : ℕ) (x : Fin n → ℕ) : Prop :=
  primeSampleGood D x ∧ ¬ ∃ p ∈ smallPrimeLabels w,
    integerPolynomialDivisibilityEvent (p.val ^ F.exponent w) D x

theorem masterPredictionPrimeGoodEvent_iff_not_bad {n : ℕ} (F : MasterParameterFamily)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (w : ℕ) (x : Fin n → ℕ) :
    masterPredictionPrimeGoodEvent F D w x ↔ ¬
      (((∃ f ∈ D, MvPolynomial.eval (fun i => (x i : ℤ)) f = 0) ∨
        (∃ i j, i ≠ j ∧ x i = x j)) ∨ ∃ p ∈ smallPrimeLabels w,
          integerPolynomialDivisibilityEvent (p.val ^ F.exponent w) D x) := by
  unfold masterPredictionPrimeGoodEvent
  rw [primeSampleGood_iff_not_bad]
  exact not_or.symm

theorem masterPredictionPrimeBadMass_bound {n : ℕ} (F : MasterParameterFamily)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (w l : ℕ) :
    event (primeIndependentMass n (F.pool w l).lower (F.pool w l).upper)
      (fun x => ¬ masterPredictionPrimeGoodEvent F D w x) ≤
      primePolynomialFamilyZeroMass (F.pool w l).lower (F.pool w l).upper D +
        primeRepeatedMass n (F.pool w l).lower (F.pool w l).upper +
          primeSmallPrimeDivisibilityProbability (F.pool w l).lower (F.pool w l).upper w D (F.exponent w) := by
  have he : (fun x => ¬ masterPredictionPrimeGoodEvent F D w x) =
      (fun x : Fin n → ℕ => ((∃ f ∈ D, MvPolynomial.eval (fun i => (x i : ℤ)) f = 0) ∨
        (∃ i j, i ≠ j ∧ x i = x j)) ∨ ∃ p ∈ smallPrimeLabels w,
          integerPolynomialDivisibilityEvent (p.val ^ F.exponent w) D x) := by
    funext x
    apply propext
    rw [masterPredictionPrimeGoodEvent_iff_not_bad, not_not]
  rw [he]
  apply (event_or_le _ _ _ (primeIndependentMass_nonneg _ _ _)).trans
  exact add_le_add (event_or_le _ _ _ (primeIndependentMass_nonneg _ _ _)) le_rfl

theorem MasterParameterConditions.prediction_prime_good_event_tendsto_one {n N : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (l : ℕ) :
    Tendsto (fun w => event (primeIndependentMass n (F.pool w l).lower (F.pool w l).upper)
      (masterPredictionPrimeGoodEvent F D w)) atTop (𝓝 1) := by
  have hz : Tendsto (fun w => primePolynomialFamilyZeroMass
      (F.pool w l).lower (F.pool w l).upper D) atTop (𝓝 0) := by
    apply (isLittleO_one_iff ℝ).mp
    simpa only [pow_zero, inv_one] using hF.polynomial_zeros l 0
  have hr : Tendsto (fun w => primeRepeatedMass n
      (F.pool w l).lower (F.pool w l).upper) atTop (𝓝 0) := by
    apply (isLittleO_one_iff ℝ).mp
    simpa only [pow_zero, inv_one] using hF.repeated_entries l 0
  have hb : Tendsto (fun w => event (primeIndependentMass n (F.pool w l).lower (F.pool w l).upper)
      (fun x => ¬ masterPredictionPrimeGoodEvent F D w x)) atTop (𝓝 0) := by
    apply squeeze_zero (fun w => event_nonneg _ _ (primeIndependentMass_nonneg _ _ _))
      (fun w => masterPredictionPrimeBadMass_bound F D w l)
    simpa only [zero_add] using (hz.add hr).add (hF.actual_small_prime l)
  have he (w : ℕ) : event (primeIndependentMass n (F.pool w l).lower (F.pool w l).upper)
      (masterPredictionPrimeGoodEvent F D w) = 1 - event
        (primeIndependentMass n (F.pool w l).lower (F.pool w l).upper)
        (fun x => ¬ masterPredictionPrimeGoodEvent F D w x) := by
    rw [event_complement, primeIndependentMass_total (hF.pool_positive_mass w l)]
    ring
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hb
  simpa only [← he, sub_zero] using h

theorem MasterParameterConditions.prediction_prime_good_event_finite_gap_tendsto_one {n N L : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (l : ℕ → Fin L) :
    Tendsto (fun w => event (primeIndependentMass n (F.pool w (l w)).lower (F.pool w (l w)).upper)
      (masterPredictionPrimeGoodEvent F D w)) atTop (𝓝 1) := by
  apply tendsto_def.mpr
  intro S hS
  have hall := eventually_all.mpr (fun j : Fin L =>
    (hF.prediction_prime_good_event_tendsto_one j.val).eventually hS)
  filter_upwards [hall] with w hw
  exact hw (l w)

theorem MasterParameterConditions.prediction_prime_good_replicas_tendsto_one {n N b L : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap : ℕ → Fin b → Fin L) :
    Tendsto (fun w => event (piMass (fun q : Fin b => primeIndependentMass n
      (F.pool w (gap w q)).lower (F.pool w (gap w q)).upper))
      (fun x => ∀ q, masterPredictionPrimeGoodEvent F D w (x q))) atTop (𝓝 1) := by
  have h := tendsto_finsetProd Finset.univ (fun q _ =>
    hF.prediction_prime_good_event_finite_gap_tendsto_one (fun w => gap w q))
  have hfun : (fun w => event (piMass (fun q : Fin b => primeIndependentMass n
      (F.pool w (gap w q)).lower (F.pool w (gap w q)).upper))
      (fun x => ∀ q, masterPredictionPrimeGoodEvent F D w (x q))) =
      (fun w => ∏ q, event (primeIndependentMass n
        (F.pool w (gap w q)).lower (F.pool w (gap w q)).upper)
        (masterPredictionPrimeGoodEvent F D w)) := by
    funext w
    exact event_piMass_all _ _
  rw [hfun]
  simpa only [Finset.prod_const_one] using h

theorem MasterParameterConditions.prediction_prime_good_replica_masses_eventually_positive {n N b L : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap : ℕ → Fin b → Fin L) :
    ∀ᶠ w in atTop, ∀ q, 0 < event (primeIndependentMass n
      (F.pool w (gap w q)).lower (F.pool w (gap w q)).upper)
      (masterPredictionPrimeGoodEvent F D w) := by
  apply eventually_all.mpr
  intro q
  exact (hF.prediction_prime_good_event_finite_gap_tendsto_one (fun w => gap w q)).eventually
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))

theorem MasterParameterConditions.prediction_good_conditioned_replicas_zero_limit {n N b L : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap : ℕ → Fin b → Fin L)
    (f : ℕ → (Fin b → Fin n → ℕ) → ℝ)
    (hf : Tendsto (fun w => expectation (piMass (fun q : Fin b => primeIndependentMass n
      (F.pool w (gap w q)).lower (F.pool w (gap w q)).upper))
      (fun x => if ∀ q, masterPredictionPrimeGoodEvent F D w (x q) then f w x else 0))
      atTop (𝓝 0)) :
    Tendsto (fun w => expectation (piMass (fun q : Fin b => conditionMass (primeIndependentMass n
      (F.pool w (gap w q)).lower (F.pool w (gap w q)).upper)
      (masterPredictionPrimeGoodEvent F D w))) (f w)) atTop (𝓝 0) := by
  apply conditioned_replicas_zero_limit _ _ f
    (fun q => hF.prediction_prime_good_event_finite_gap_tendsto_one (fun w => gap w q))
  convert hf using 1
  funext w
  apply congrArg (expectation (piMass (fun q : Fin b => primeIndependentMass n
    (F.pool w (gap w q)).lower (F.pool w (gap w q)).upper)))
  funext x
  split_ifs <;> rfl

end Hindman168
