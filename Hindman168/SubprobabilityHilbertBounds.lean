import Hindman168.FiniteMassHilbertClipping

/-! Uniform norm bounds for original subprobability laws, including zero laws. -/
namespace Hindman168
open FiniteMass Filter
open scoped BigOperators
variable {α : Type*}

theorem finiteMassL2_norm_le_subprob (μ : Mass α) [hμ : Fact (∀ a, 0 ≤ μ a)]
    (hprob : total μ ≤ 1) (f : FiniteMassL2 μ) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ a ∈ μ.support, |f a| ≤ B) : ‖f‖ ≤ B := by
  have hs : ‖f‖ ^ 2 ≤ B ^ 2 := by
    rw [finiteMassL2_norm_sq]
    calc
      expectation μ (fun a => f a ^ 2) ≤ ∑ a ∈ μ.support, μ a * B ^ 2 := by
        apply Finset.sum_le_sum
        intro a ha
        apply mul_le_mul_of_nonneg_left _ (hμ.out a)
        have hh := (sq_le_sq₀ (abs_nonneg (f a)) hB).mpr (hf a ha)
        simpa only [sq_abs] using hh
      _ = total μ * B ^ 2 := by rw [← Finset.sum_mul]; rfl
      _ ≤ B ^ 2 := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hprob (sq_nonneg B)
  nlinarith [norm_nonneg f]



variable (μ : ℕ → Mass α) [∀ w, Fact (∀ a, 0 ≤ μ w a)]

noncomputable def subprobabilityBoundedFamily (hprob : ∀ w, total (μ w) ≤ 1)
    (f : ℕ → α → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ w a, a ∈ (μ w).support → |f w a| ≤ B) :
    boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)) :=
  ⟨f, B, hB, fun w => finiteMassL2_norm_le_subprob (μ w) (hprob w) (f w) hB (hf w)⟩
noncomputable def subprobabilityClipFamily (hprob : ∀ w, total (μ w) ≤ 1)
    (x : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w))) :
    boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)) :=
  subprobabilityBoundedFamily μ hprob (fun w a => unitIntervalClip (x.val w a)) 1 (by norm_num)
    (fun w a _ => by
      rw [abs_of_nonneg (unitIntervalClip_bounds _).1]
      exact (unitIntervalClip_bounds _).2)

theorem subprobabilityHilbert_clip_distance_le (U : Ultrafilter ℕ) (hprob : ∀ w, total (μ w) ≤ 1)
    (f t : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)))
    (hf : ∀ w a, a ∈ (μ w).support → 0 ≤ f.val w a ∧ f.val w a ≤ 1) :
    ‖hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U (subprobabilityClipFamily μ hprob t)‖ ≤
      ‖hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U t‖ := by
  have hs := le_of_tendsto_of_tendsto
    (hilbertFamilyToCompletion_norm_sub_sq_tendsto _ U f (subprobabilityClipFamily μ hprob t))
    (hilbertFamilyToCompletion_norm_sub_sq_tendsto _ U f t)
    (Eventually.of_forall (fun w => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (finiteMassL2_clip_distance_le (μ w) (f.val w) (t.val w) (hf w))))
  nlinarith [norm_nonneg (hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U t),
    norm_nonneg (hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U (subprobabilityClipFamily μ hprob t))]

end Hindman168

