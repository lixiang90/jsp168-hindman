import Hindman168.HomeomorphSingletonDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! The actual differential of a genuine coordinate homeomorphism in
its constructed singleton chart is identity. The actual chart reads
that homeomorphism as identity in the original normed model. -/

namespace Hindman168
open Function Set
open scoped Manifold ContDiff

variable {F Q : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace Q] [Nonempty Q]

theorem homeomorphSingleton_hasMFDerivAt (e : F ≃ₜ Q) (x : F) :
    letI := homeomorphSingletonChart e
    HasMFDerivAt 𝓘(ℝ, F) 𝓘(ℝ, F) e x (ContinuousLinearMap.id ℝ F) := by
  letI := homeomorphSingletonChart e
  refine ⟨e.continuous.continuousAt, ?_⟩
  simp only [writtenInExtChartAt, mfld_simps]
  change HasFDerivWithinAt (fun y : F => e.symm (e y)) (ContinuousLinearMap.id ℝ F) univ x
  have he : (fun y : F => e.symm (e y)) = id := funext e.symm_apply_apply
  rw [he]
  exact (hasFDerivAt_id x).hasFDerivWithinAt

theorem homeomorphSingleton_mfderiv (e : F ≃ₜ Q) (x : F) :
    letI := homeomorphSingletonChart e
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) e x = ContinuousLinearMap.id ℝ F := by
  letI := homeomorphSingletonChart e
  exact (homeomorphSingleton_hasMFDerivAt e x).mfderiv

end Hindman168
