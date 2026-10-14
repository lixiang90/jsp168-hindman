import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! A genuine homeomorphism from a real normed model equips its actual
target topology with a single global smooth chart. Smoothness here is
only smoothness of this constructed coordinate identification; no target
algebraic operation is assumed smooth. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {F Q : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace Q] [Nonempty Q]

@[reducible]
noncomputable def homeomorphSingletonChart (e : F ≃ₜ Q) : ChartedSpace F Q :=
  e.symm.isOpenEmbedding.singletonChartedSpace

theorem homeomorphSingletonChart_isManifold (e : F ≃ₜ Q) :
    letI := homeomorphSingletonChart e
    IsManifold 𝓘(ℝ, F) ∞ Q :=
  e.symm.isOpenEmbedding.isManifold_singleton

noncomputable def homeomorphSingletonDiffeomorph (e : F ≃ₜ Q) :
    letI := homeomorphSingletonChart e
    Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) F Q ∞ := by
  letI := homeomorphSingletonChart e
  refine { e.toEquiv with contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · have h : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (e.symm ∘ (e : F → Q)) := by
      have he : e.symm ∘ (e : F → Q) = (id : F → F) := funext e.symm_apply_apply
      rw [he]
      exact contMDiff_id
    exact h.of_comp_isOpenEmbedding e.symm.isOpenEmbedding
  · exact contMDiff_isOpenEmbedding e.symm.isOpenEmbedding

end Hindman168
