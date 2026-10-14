import Hindman168.MaskRootCopiedMajorant
import Hindman168.MaskCopiedNormalizedMoments

/-! Normalization by the original good-prime event, whose probability is
already proved to approach one. Every enlarged subset has the expected
power-of-two majorant mean under this unchanged conditional law. -/

set_option maxHeartbeats 2000000

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

namespace MaskRootCopiedSampling

variable {m N : ℕ}

theorem conditioned_prime_probability_eventually (S : MaskRootCopiedSampling m N) :
    ∀ᶠ w in atTop,
      (∀ x, 0 ≤ conditionMass (S.primeMass w) (maskGeneratedCopiedPrimeGood m S.gap S.template w) x) ∧
      total (conditionMass (S.primeMass w) (maskGeneratedCopiedPrimeGood m S.gap S.template w)) = 1 := by
  have hF := maskGeneratedMaster_conditions m S.gap (∅ : Finset ℚ) (by simp)
  filter_upwards [(maskGeneratedCopiedGood_event_tendsto_one m S.gap S.template).eventually
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))] with w hw
  exact ⟨conditionMass_nonneg _ _ (hF.prime_slots_nonneg w (fun _ => (S.gap w).val)),
    conditionMass_total _ _ hw⟩

noncomputable def normalizedMajorant (S : MaskRootCopiedSampling m N) {q : ℕ}
    (label : ℕ → Fin q → Fin (m + 1)) (row : ℕ → Fin q → MaskRootCopiedRow m S.gap S.template)
    (U : Finset (Fin q)) (w : ℕ) : ℝ :=
  expectation (conditionMass (S.primeMass w) (maskGeneratedCopiedPrimeGood m S.gap S.template w))
    (fun x => expectation (S.baseMass w x) (fun y => ∏ u ∈ U, (1 + S.weight label row w u x y)))

theorem normalizedMajorant_eq (S : MaskRootCopiedSampling m N) {q : ℕ}
    (label : ℕ → Fin q → Fin (m + 1)) (row : ℕ → Fin q → MaskRootCopiedRow m S.gap S.template)
    (U : Finset (Fin q)) (w : ℕ) :
    S.normalizedMajorant label row U w =
      conditionalFiniteAverage (S.primeMass w) (S.baseMass w)
        (maskGeneratedCopiedPrimeGood m S.gap S.template w)
        (fun x y => ∏ u ∈ U, (1 + S.weight label row w u x y)) /
          event (S.primeMass w) (maskGeneratedCopiedPrimeGood m S.gap S.template w) := by
  unfold normalizedMajorant
  rw [expectation_conditionMass]
  rfl

theorem normalizedMajorant_tendsto (S : MaskRootCopiedSampling m N) {q : ℕ}
    (label : ℕ → Fin q → Fin (m + 1)) (row : ℕ → Fin q → MaskRootCopiedRow m S.gap S.template)
    (hrow : ∀ᶠ w in atTop, Function.Injective (row w))
    (hdivbudget : ∀ᶠ w in atTop, ∀ u,
      tailBound ((S.chain w).tailCutoffs ((maskGeneratedMaster m S.gap).cutoff w) (label w u)) ≤ S.budget w)
    (U : Finset (Fin q)) :
    Tendsto (S.normalizedMajorant label row U) atTop (𝓝 (((2 ^ U.card : ℕ) : ℝ))) := by
  have hp : Tendsto (fun w => event (S.primeMass w)
      (maskGeneratedCopiedPrimeGood m S.gap S.template w)) atTop (𝓝 1) :=
    maskGeneratedCopiedGood_event_tendsto_one m S.gap S.template
  have hm := S.majorant_mean_tendsto label row hrow hdivbudget U
  have hn := hm.add ((tendsto_const_nhds (x := ((2 ^ U.card : ℕ) : ℝ))).mul hp)
  simp only [sub_add_cancel, mul_one, zero_add] at hn
  have hd := hn.div hp (by norm_num : (1 : ℝ) ≠ 0)
  have he := hd.congr (fun w => (S.normalizedMajorant_eq label row U w).symm)
  simpa only [div_one] using he

end MaskRootCopiedSampling
end Hindman168
