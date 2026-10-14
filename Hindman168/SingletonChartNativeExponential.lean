import Hindman168.HomeomorphSingletonDifferential
import Hindman168.LieOneParameterVelocity
import Hindman168.NativeLieGlobalLogarithm

/-! A genuine exponential coordinate homeomorphism is identified with the
native Lie exponential by its proved singleton-chart differential and the
actual ray subgroup law. No compatibility identity is assumed. -/
namespace Hindman168
open scoped Manifold ContDiff

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace A] [Group A] [T2Space A]

theorem homeomorph_singleton_native_exponential (e : E ≃ₜ A)
    (hLie : letI := homeomorphSingletonChart e; LieGroup 𝓘(ℝ,E) ∞ A)
    (h0 : e 0=1)
    (hadd : ∀ (v : E) (r s : ℝ), e ((r+s) • v)=e (r • v)*e (s • v)) :
    letI := homeomorphSingletonChart e
    letI := hLie
    letI : LieGroup 𝓘(ℝ,E) (minSmoothness ℝ 3) A := lieGroup_smooth_min_three
    ∀ v : E, nativeLieExponential (I := 𝓘(ℝ,E)) (G := A) v=e v := by
  letI := homeomorphSingletonChart e
  letI := hLie
  letI : LieGroup 𝓘(ℝ,E) (minSmoothness ℝ 3) A := lieGroup_smooth_min_three
  intro v
  have hcurve0 : e ((0 : ℝ) • v)=1 := by rw [zero_smul]; exact h0
  have hderiv : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ,E) (fun t : ℝ => e (t • v)) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight v) := by
    have hray : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ,E) (fun t : ℝ => t • v) 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight v) :=
      ((1 : ℝ →L[ℝ] ℝ).smulRight v).hasFDerivAt.hasMFDerivAt
    have he := homeomorphSingleton_hasMFDerivAt e ((0 : ℝ) • v)
    exact (he.comp 0 hray).congr_mfderiv (ContinuousLinearMap.id_comp _)
  have h := nativeLieExponential_eq_oneParameter_from_zero v hcurve0 (hadd v) hderiv
  simpa only [one_smul] using h

variable [FiniteDimensional ℝ E] [Group.IsNilpotent A] [ConnectedSpace A] [SimplyConnectedSpace A]

theorem homeomorph_singleton_native_logarithm (e : E ≃ₜ A)
    (hLie : letI := homeomorphSingletonChart e; LieGroup 𝓘(ℝ,E) ∞ A)
    (h0 : e 0=1)
    (hadd : ∀ (v : E) (r s : ℝ), e ((r+s) • v)=e (r • v)*e (s • v)) :
    letI := homeomorphSingletonChart e
    letI := hLie
    ∀ a : A, nativeLieGlobalLogarithm (E := E) (I := 𝓘(ℝ,E)) (G := A) a=e.symm a := by
  letI := homeomorphSingletonChart e
  letI := hLie
  intro a
  apply e.injective
  rw [e.apply_symm_apply]
  rw [←homeomorph_singleton_native_exponential e hLie h0 hadd]
  exact nativeLieExponential_globalLogarithm (E := E) (I := 𝓘(ℝ,E)) (G := A) a

end Hindman168
