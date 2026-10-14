import Hindman168.ReplicaPrimeSlots
import Hindman168.MasterPredictionGoodTupleLaw

/-!
# Original local good-tuple laws with the preprint's denominator exclusion

Polynomial zeros and repeated local primes are excluded, together with
small-prime powers dividing one chosen denominator polynomial. This is the
preprint's event shape, rather than excluding divisibility of every test
polynomial. Renamed local test families included in the master list imply
probability tending to one by exact marginalization and event monotonicity.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

def predictionLocalPrimeGoodEvent {k : ℕ} (F : MasterParameterFamily)
    (T : Finset (MvPolynomial (Fin k) ℤ)) (den : MvPolynomial (Fin k) ℤ)
    (w : ℕ) (x : Fin k → ℕ) : Prop :=
  primeSampleGood T x ∧ ¬ ∃ p ∈ smallPrimeLabels w,
    ((p.val ^ F.exponent w : ℕ) : ℤ) ∣ MvPolynomial.eval (fun i => (x i : ℤ)) den

theorem predictionLocalPrimeGoodEvent_den_nonzero {k : ℕ} (F : MasterParameterFamily)
    (T : Finset (MvPolynomial (Fin k) ℤ)) (den : MvPolynomial (Fin k) ℤ)
    (hden : den ∈ T) (w : ℕ) (x : Fin k → ℕ) (hx : predictionLocalPrimeGoodEvent F T den w x) :
    MvPolynomial.eval (fun i => (x i : ℤ)) den ≠ 0 := hx.1.2 den hden

theorem master_good_implies_local_good {n k : ℕ} (F : MasterParameterFamily)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (T : Finset (MvPolynomial (Fin k) ℤ))
    (den : MvPolynomial (Fin k) ℤ) (hden : den ∈ T) (j : Fin k → Fin n)
    (hj : Function.Injective j) (hT : ∀ f ∈ T, MvPolynomial.rename j f ∈ D)
    (w : ℕ) (x : Fin n → ℕ) (hx : masterPredictionPrimeGoodEvent F D w x) :
    predictionLocalPrimeGoodEvent F T den w (fun i => x (j i)) := by
  refine ⟨⟨hx.1.1.comp hj, ?_⟩, ?_⟩
  · intro f hf
    have h := hx.1.2 (MvPolynomial.rename j f) (hT f hf)
    simpa only [MvPolynomial.eval_rename, Function.comp_def] using h
  · rintro ⟨p, hp, hd⟩
    apply hx.2
    refine ⟨p, hp, MvPolynomial.rename j den, hT den hden, ?_⟩
    simpa only [MvPolynomial.eval_rename, Function.comp_def] using hd

theorem MasterParameterConditions.local_prime_pool_projection {n N k : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (j : Fin k → Fin n)
    (hj : Function.Injective j) (w l : ℕ) :
    (primeIndependentMass n (F.pool w l).lower (F.pool w l).upper).mapDomain
      (fun x i => x (j i)) = primeIndependentMass k (F.pool w l).lower (F.pool w l).upper := by
  exact piMass_restrict _ j hj (fun _ => primePoolMass_total (hF.pool_positive_mass w l))

theorem MasterParameterConditions.local_prime_good_event_tendsto_one {n N k L : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F)
    (T : Finset (MvPolynomial (Fin k) ℤ)) (den : MvPolynomial (Fin k) ℤ) (hden : den ∈ T)
    (j : Fin k → Fin n) (hj : Function.Injective j)
    (hT : ∀ f ∈ T, MvPolynomial.rename j f ∈ D) (gap : ℕ → Fin L) :
    Tendsto (fun w => event (primeIndependentMass k (F.pool w (gap w)).lower (F.pool w (gap w)).upper)
      (predictionLocalPrimeGoodEvent F T den w)) atTop (𝓝 1) := by
  have hlo (w : ℕ) : event (primeIndependentMass n (F.pool w (gap w)).lower (F.pool w (gap w)).upper)
      (masterPredictionPrimeGoodEvent F D w) ≤
      event (primeIndependentMass k (F.pool w (gap w)).lower (F.pool w (gap w)).upper)
        (predictionLocalPrimeGoodEvent F T den w) := by
    rw [← hF.local_prime_pool_projection j hj w (gap w), event_map]
    exact event_mono _ (primeIndependentMass_nonneg _ _ _)
      (fun x hx => master_good_implies_local_good F D T den hden j hj hT w x hx)
  have hhi (w : ℕ) : event (primeIndependentMass k (F.pool w (gap w)).lower (F.pool w (gap w)).upper)
      (predictionLocalPrimeGoodEvent F T den w) ≤ 1 := by
    exact (event_le_total _ _ (primeIndependentMass_nonneg _ _ _)).trans_eq
      (primeIndependentMass_total (hF.pool_positive_mass w (gap w)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (hF.prediction_prime_good_event_finite_gap_tendsto_one gap) tendsto_const_nhds hlo hhi

theorem MasterParameterConditions.local_prime_good_mass_eventually_positive {n N k L : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F)
    (T : Finset (MvPolynomial (Fin k) ℤ)) (den : MvPolynomial (Fin k) ℤ) (hden : den ∈ T)
    (j : Fin k → Fin n) (hj : Function.Injective j)
    (hT : ∀ f ∈ T, MvPolynomial.rename j f ∈ D) (gap : ℕ → Fin L) :
    ∀ᶠ w in atTop, 0 < event (primeIndependentMass k (F.pool w (gap w)).lower (F.pool w (gap w)).upper)
      (predictionLocalPrimeGoodEvent F T den w) :=
  (hF.local_prime_good_event_tendsto_one T den hden j hj hT gap).eventually
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))

end Hindman168
