import Hindman168.PieceNilLipschitzComposition
import Hindman168.FiniteMassUltrafilterHilbert

/-! Pointwise clipping contracts the original weighted L2 distance to
any [0,1]-valued target, and therefore contracts that distance in the
actual completed ultrafilter Hilbert space. -/

namespace Hindman168
open FiniteMass Filter

noncomputable def finiteMassL2Clip {α : Type*} (μ : Mass α) (t : FiniteMassL2 μ) : FiniteMassL2 μ :=
  fun a => unitIntervalClip (t a)

theorem finiteMassL2_clip_distance_le {α : Type*} (μ : Mass α) [hμ : Fact (∀ a, 0 ≤ μ a)]
    (f t : FiniteMassL2 μ) (hf : ∀ a ∈ μ.support, 0 ≤ f a ∧ f a ≤ 1) :
    ‖f - finiteMassL2Clip μ t‖ ≤ ‖f - t‖ := by
  have hs : ‖f - finiteMassL2Clip μ t‖ ^ 2 ≤ ‖f - t‖ ^ 2 := by
    rw [finiteMassL2_norm_sq, finiteMassL2_norm_sq]
    apply Finset.sum_le_sum
    intro a ha
    apply mul_le_mul_of_nonneg_left _ (hμ.out a)
    change (f a - unitIntervalClip (t a)) ^ 2 ≤ (f a - t a) ^ 2
    have hc := unitIntervalClip_distance_le (f a) (t a) (hf a ha)
    have hh := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hc
    simpa only [sq_abs] using hh
  nlinarith [norm_nonneg (f - t), norm_nonneg (f - finiteMassL2Clip μ t)]

variable {α : Type*} (μ : ℕ → Mass α) [∀ w, Fact (∀ a, 0 ≤ μ w a)]

noncomputable def finiteMassClipFamily (hprob : ∀ w, total (μ w) = 1)
    (x : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w))) :
    boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)) :=
  finiteMassBoundedFamily μ hprob (fun w a => unitIntervalClip (x.val w a)) 1 (by norm_num)
    (fun w a _ => by
      rw [abs_of_nonneg (unitIntervalClip_bounds _).1]
      exact (unitIntervalClip_bounds _).2)

theorem finiteMassHilbert_clip_distance_le (U : Ultrafilter ℕ) (hprob : ∀ w, total (μ w) = 1)
    (f t : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)))
    (hf : ∀ w a, a ∈ (μ w).support → 0 ≤ f.val w a ∧ f.val w a ≤ 1) :
    ‖hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U (finiteMassClipFamily μ hprob t)‖ ≤
      ‖hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U t‖ := by
  have hs := le_of_tendsto_of_tendsto
    (hilbertFamilyToCompletion_norm_sub_sq_tendsto _ U f (finiteMassClipFamily μ hprob t))
    (hilbertFamilyToCompletion_norm_sub_sq_tendsto _ U f t)
    (Eventually.of_forall (fun w => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (finiteMassL2_clip_distance_le (μ w) (f.val w) (t.val w) (hf w))))
  nlinarith [norm_nonneg (hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U t),
    norm_nonneg (hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U (finiteMassClipFamily μ hprob t))]

end Hindman168
