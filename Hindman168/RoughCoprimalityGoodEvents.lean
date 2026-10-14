import Hindman168.RoughCoprimalityLimits

/-!
# Nonzero coprime rough polynomial values have probability tending to one

The good event is the exact complement of product zero or a nontrivial
rough gcd. Positivity of the actual rough parts is used in this equivalence.
The joint mass is eventually one for the original growing pool laws, and
also for separately conditioned laws whose event masses tend to one.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

def roughPolynomialGoodEvent {m n : ℕ} (w : ℕ)
    (F : MvPolynomial (Fin m) ℤ) (G : MvPolynomial (Fin n) ℤ)
    (xy : (Fin m → ℕ) × (Fin n → ℕ)) : Prop :=
  MvPolynomial.eval (fun i => (xy.1 i : ℤ)) F *
    MvPolynomial.eval (fun i => (xy.2 i : ℤ)) G ≠ 0 ∧
  (roughPartNat w (MvPolynomial.eval (fun i => (xy.1 i : ℤ)) F).natAbs).Coprime
    (roughPartNat w (MvPolynomial.eval (fun i => (xy.2 i : ℤ)) G).natAbs)

theorem roughPolynomialGoodEvent_iff_not_bad {m n w : ℕ}
    (F : MvPolynomial (Fin m) ℤ) (G : MvPolynomial (Fin n) ℤ)
    (xy : (Fin m → ℕ) × (Fin n → ℕ)) :
    roughPolynomialGoodEvent w F G xy ↔
      ¬ (polynomialProductZeroEvent F G xy ∨ roughPolynomialGcdEvent w F G xy) := by
  unfold roughPolynomialGoodEvent polynomialProductZeroEvent roughPolynomialGcdEvent
  by_cases h : MvPolynomial.eval (fun i => (xy.1 i : ℤ)) F *
      MvPolynomial.eval (fun i => (xy.2 i : ℤ)) G = 0
  · simp only [h, ne_eq, not_true_eq_false, false_and, true_or, not_true_eq_false]
  · have hF := (mul_ne_zero_iff.mp h).1
    have hg : 0 < (roughPartNat w (MvPolynomial.eval (fun i => (xy.1 i : ℤ)) F).natAbs).gcd
        (roughPartNat w (MvPolynomial.eval (fun i => (xy.2 i : ℤ)) G).natAbs) :=
      Nat.gcd_pos_of_pos_left _ (roughPartNat_pos (Int.natAbs_ne_zero.mpr hF))
    unfold Nat.Coprime
    simp only [h, false_or]
    omega

theorem roughPolynomialGoodEvent_mass_complement {m n w : ℕ}
    (μ : Mass (Fin m → ℕ)) (ν : Mass (Fin n → ℕ))
    (F : MvPolynomial (Fin m) ℤ) (G : MvPolynomial (Fin n) ℤ) :
    event (tensor μ ν) (roughPolynomialGoodEvent w F G) = total (tensor μ ν) -
      event (tensor μ ν) (fun xy => polynomialProductZeroEvent F G xy ∨ roughPolynomialGcdEvent w F G xy) := by
  have hE : roughPolynomialGoodEvent w F G =
      (fun xy => ¬ (polynomialProductZeroEvent F G xy ∨ roughPolynomialGcdEvent w F G xy)) := by
    funext xy
    exact propext (roughPolynomialGoodEvent_iff_not_bad F G xy)
  rw [hE, event_complement]

theorem dyadicPoolTupleMass_eventually_total_one {n : ℕ}
    (P : ℕ → Fin n → DyadicPrimePool) (hP : ∀ w i, w ≤ (P w i).lowerExponent) :
    ∀ᶠ w in atTop, total (dyadicPoolTupleMass (P w)) = 1 := by
  obtain ⟨en, hen⟩ := exists_dyadic_prime_normalization_threshold
  filter_upwards [eventually_ge_atTop en] with w hw
  apply dyadicPoolTupleMass_total
  intro i
  exact (P w i).harmonicMass_pos_of_first (hen _ (hw.trans (hP w i)))

theorem roughPolynomialGoodEvent_tendsto_one_of_bad_limits {m n : ℕ}
    (F : MvPolynomial (Fin m) ℤ) (G : MvPolynomial (Fin n) ℤ)
    (μ : ℕ → Mass (Fin m → ℕ)) (ν : ℕ → Mass (Fin n → ℕ))
    (hμ : ∀ w x, 0 ≤ μ w x) (hν : ∀ w y, 0 ≤ ν w y)
    (htμ : ∀ᶠ w in atTop, total (μ w) = 1) (htν : ∀ᶠ w in atTop, total (ν w) = 1)
    (hz : Tendsto (fun w => event (tensor (μ w) (ν w)) (polynomialProductZeroEvent F G)) atTop (𝓝 0))
    (hg : Tendsto (fun w => event (tensor (μ w) (ν w)) (roughPolynomialGcdEvent w F G)) atTop (𝓝 0)) :
    Tendsto (fun w => event (tensor (μ w) (ν w)) (roughPolynomialGoodEvent w F G)) atTop (𝓝 1) := by
  have hb : Tendsto (fun w => event (tensor (μ w) (ν w))
      (fun xy => polynomialProductZeroEvent F G xy ∨ roughPolynomialGcdEvent w F G xy)) atTop (𝓝 0) := by
    apply squeeze_zero (fun w => event_nonneg _ _ (tensor_nonneg _ _ (hμ w) (hν w)))
      (fun w => event_or_le _ _ _ (tensor_nonneg _ _ (hμ w) (hν w)))
    simpa only [zero_add] using hz.add hg
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hb
  have hident : (fun w => 1 - event (tensor (μ w) (ν w))
      (fun xy => polynomialProductZeroEvent F G xy ∨ roughPolynomialGcdEvent w F G xy)) =ᶠ[atTop]
      (fun w => event (tensor (μ w) (ν w)) (roughPolynomialGoodEvent w F G)) := by
    filter_upwards [htμ, htν] with w hwμ hwν
    rw [roughPolynomialGoodEvent_mass_complement, tensor_total, hwμ, hwν, one_mul]
  simpa only [sub_zero] using ht.congr' hident

theorem dyadicPool_rough_good_tendsto_one {m n : ℕ}
    {F : MvPolynomial (Fin m) ℤ} {G : MvPolynomial (Fin n) ℤ}
    (hF : F ≠ 0) (hG : G ≠ 0)
    (PF : ℕ → Fin m → DyadicPrimePool) (PG : ℕ → Fin n → DyadicPrimePool)
    (hPF : ∀ w i, w ≤ (PF w i).lowerExponent) (hPG : ∀ w i, w ≤ (PG w i).lowerExponent) :
    Tendsto (fun w => event (tensor (dyadicPoolTupleMass (PF w)) (dyadicPoolTupleMass (PG w)))
      (roughPolynomialGoodEvent w F G)) atTop (𝓝 1) := by
  obtain ⟨hz, hg⟩ := dyadicPool_bad_events_tendsto_zero hF hG PF PG hPF hPG
  exact roughPolynomialGoodEvent_tendsto_one_of_bad_limits F G _ _
    (fun w => dyadicPoolTupleMass_nonneg (PF w)) (fun w => dyadicPoolTupleMass_nonneg (PG w))
    (dyadicPoolTupleMass_eventually_total_one PF hPF) (dyadicPoolTupleMass_eventually_total_one PG hPG) hz hg

theorem conditioned_dyadicPool_rough_good_tendsto_one {m n : ℕ}
    {F : MvPolynomial (Fin m) ℤ} {G : MvPolynomial (Fin n) ℤ}
    (hF : F ≠ 0) (hG : G ≠ 0)
    (PF : ℕ → Fin m → DyadicPrimePool) (PG : ℕ → Fin n → DyadicPrimePool)
    (hPF : ∀ w i, w ≤ (PF w i).lowerExponent) (hPG : ∀ w i, w ≤ (PG w i).lowerExponent)
    (A : ℕ → (Fin m → ℕ) → Prop) (C : ℕ → (Fin n → ℕ) → Prop)
    (hA : Tendsto (fun w => event (dyadicPoolTupleMass (PF w)) (A w)) atTop (𝓝 1))
    (hC : Tendsto (fun w => event (dyadicPoolTupleMass (PG w)) (C w)) atTop (𝓝 1)) :
    Tendsto (fun w => event
      (tensor (conditionMass (dyadicPoolTupleMass (PF w)) (A w)) (conditionMass (dyadicPoolTupleMass (PG w)) (C w)))
      (roughPolynomialGoodEvent w F G)) atTop (𝓝 1) := by
  obtain ⟨hz, hg⟩ := conditioned_dyadicPool_bad_events_tendsto_zero hF hG PF PG hPF hPG A C hA hC
  have htF : ∀ᶠ w in atTop, total (conditionMass (dyadicPoolTupleMass (PF w)) (A w)) = 1 :=
    (hA.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun w hw => conditionMass_total _ _ hw)
  have htG : ∀ᶠ w in atTop, total (conditionMass (dyadicPoolTupleMass (PG w)) (C w)) = 1 :=
    (hC.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun w hw => conditionMass_total _ _ hw)
  exact roughPolynomialGoodEvent_tendsto_one_of_bad_limits F G _ _
    (fun w => conditionMass_nonneg _ _ (dyadicPoolTupleMass_nonneg (PF w)))
    (fun w => conditionMass_nonneg _ _ (dyadicPoolTupleMass_nonneg (PG w))) htF htG hz hg

end Hindman168
