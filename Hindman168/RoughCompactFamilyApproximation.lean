import Hindman168.RoughUniformLipschitzApproximation

namespace Hindman168

theorem rough_compact_family_lipschitz_approximation {A X Y : Type*}
    [PseudoMetricSpace A] [CompactSpace A] [PseudoMetricSpace X] [CompactSpace X]
    [Nonempty X] [PseudoMetricSpace Y] (φ : A × X → Y) (hφ : Continuous φ)
    (B : ℝ) (hB : 0 ≤ B) (L : NNReal) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : NNReal, ∀ (a : A) (F : Y → ℝ), LipschitzWith L F →
      (∀ y, |F y| ≤ B) → ∃ g : X → ℝ, LipschitzWith K g ∧
        (∀ x, |F (φ (a, x)) - g x| ≤ ε) ∧ (∀ x, |g x| ≤ B) := by
  have hLp : 0 < (L : ℝ) + 1 := by positivity
  obtain ⟨δ, hδ, hm⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hφ) (ε / ((L : ℝ) + 1))
    (div_pos hε hLp)
  obtain ⟨K, hK⟩ := rough_uniform_lipschitz_approximation (X := X) B δ ε hB hδ hε.le
  refine ⟨K, ?_⟩
  intro a F hF hbound
  apply hK (fun x => F (φ (a, x))) (fun x => hbound _)
  intro x y hxy
  have hp : dist (a, x) (a, y) < δ := by
    simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hxy
  have hdist := hm hp
  have he : (L : ℝ) * (ε / ((L : ℝ) + 1)) < ε := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hLp).mpr
    nlinarith
  exact ((hF.dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left hdist.le L.coe_nonneg)).trans he.le

end Hindman168
