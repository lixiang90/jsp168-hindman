import Hindman168.NativeLieGlobalTopology
import Hindman168.NativeLieExponentialDiffeomorph
import Hindman168.NativeLieDexpDeterminant
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! The ORIGINAL left translation expressed in the proved global log
coordinates. Its derivative is related to ORIGINAL dexp by actual chain rules. -/

namespace Hindman168
open Function
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [IsTopologicalGroup G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLogLeftTranslationHomeomorph (g : G) : E ≃ₜ E :=
  ((nativeLieGlobalExponentialHomeomorph (E := E) (I := I) (G := G)).trans (Homeomorph.mulLeft g)).trans
    (nativeLieGlobalExponentialHomeomorph (E := E) (I := I) (G := G)).symm

theorem native_log_left_translation_apply (g : G) (v : E) :
    nativeLogLeftTranslationHomeomorph (E := E) (I := I) g v =
      nativeLieGlobalLogarithm (E := E) (I := I) (g*nativeLieExponential (E := E) (I := I) (G := G) v) := rfl

theorem native_log_left_translation_contDiff (g : G) :
    ContDiff ℝ ∞ (nativeLogLeftTranslationHomeomorph (E := E) (I := I) g) := by
  have hm := (nativeLieGlobalLogarithm_contMDiff (E := E) (I := I) (G := G)).comp
    ((contMDiff_mul_left : ContMDiff I I ∞ (fun x : G => g*x)).comp
      (nativeLieExponential_contMDiff (I := I) (G := G)))
  exact hm.contDiff

theorem native_log_left_translation_dexp_derivative (g : G) (v : E) :
    (nativeLieDexp (I := I) (G := G) (nativeLogLeftTranslationHomeomorph (E := E) (I := I) g v)).comp
      (fderiv ℝ (nativeLogLeftTranslationHomeomorph (E := E) (I := I) g) v) =
        nativeLieDexp (I := I) (G := G) v := by
  let T := nativeLogLeftTranslationHomeomorph (E := E) (I := I) g
  let exp : E → G := nativeLieExponential (E := E) (I := I) (G := G)
  let u : E := T v
  let A : G → G := fun h => (exp u)⁻¹*h
  let B : G → G := fun h => (exp v)⁻¹*h
  let P : E → G := A ∘ exp
  let R : E → G := B ∘ exp
  have hu : exp u = g*exp v := nativeLieExponential_globalLogarithm (I := I) (g*exp v)
  have hExp : MDifferentiable 𝓘(ℝ, E) I exp :=
    (nativeLieExponential_contMDiff (I := I) (G := G)).mdifferentiable (by norm_num)
  have hA : MDifferentiable I I A :=
    (contMDiff_mul_left : ContMDiff I I ∞ A).mdifferentiable (by norm_num)
  have hB : MDifferentiable I I B :=
    (contMDiff_mul_left : ContMDiff I I ∞ B).mdifferentiable (by norm_num)
  have hP : MDifferentiable 𝓘(ℝ, E) I P := hA.comp hExp
  have hT : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) T :=
    (native_log_left_translation_contDiff (I := I) g).contMDiff.mdifferentiable (by norm_num)
  have hPu : mfderiv 𝓘(ℝ, E) I P u = nativeLieDexp (I := I) (G := G) u := by
    rw [show P = A ∘ exp from rfl, mfderiv_comp u (hA (exp u)) (hExp u)]
    rfl
  have hRv : mfderiv 𝓘(ℝ, E) I R v = nativeLieDexp (I := I) (G := G) v := by
    rw [show R = B ∘ exp from rfl, mfderiv_comp v (hB (exp v)) (hExp v)]
    rfl
  have he : P ∘ T = R := by
    funext y
    change (exp u)⁻¹*exp (T y) = (exp v)⁻¹*exp y
    have hy : exp (T y) = g*exp y := nativeLieExponential_globalLogarithm (I := I) (g*exp y)
    rw [hy, hu]
    group
  have hm := mfderiv_comp v (hP (T v)) (hT v)
  rw [he] at hm
  change mfderiv 𝓘(ℝ, E) I R v =
    (mfderiv 𝓘(ℝ, E) I P u).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) T v) at hm
  rw [hPu, hRv, mfderiv_eq_fderiv] at hm
  exact hm.symm

theorem native_log_left_translation_derivative_det_one (g : G) (v : E) :
    LinearMap.det (fderiv ℝ (nativeLogLeftTranslationHomeomorph (E := E) (I := I) g) v).toLinearMap = 1 := by
  have hm := congrArg (fun L : E →L[ℝ] E => LinearMap.det L.toLinearMap)
    (native_log_left_translation_dexp_derivative (I := I) g v)
  change LinearMap.det ((nativeLieDexp (I := I) (G := G)
      (nativeLogLeftTranslationHomeomorph (E := E) (I := I) g v)).toLinearMap *
      (fderiv ℝ (nativeLogLeftTranslationHomeomorph (E := E) (I := I) g) v).toLinearMap) =
        LinearMap.det (nativeLieDexp (I := I) (G := G) v).toLinearMap at hm
  rwa [map_mul, native_lie_dexp_determinant_one, native_lie_dexp_determinant_one, one_mul] at hm

end Hindman168
