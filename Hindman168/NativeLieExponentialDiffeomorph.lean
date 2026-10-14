import Hindman168.NativeLieGlobalLogarithm
import Mathlib.Geometry.Manifold.Diffeomorph

/-! The genuine global logarithm is smooth by identification with the
actual local inverse near every original group point. Thus the actual
original exponential, with its proved covering-derived inverse, is a
global native C-infinity diffeomorphism. No global inverse is assumed. -/

namespace Hindman168
open Function Set Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieGlobalLogarithm_contMDiff :
    ContMDiff I 𝓘(ℝ, E) ∞
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) : G → E) := by
  intro g
  obtain ⟨v, rfl⟩ := nativeLieExponential_surjective (E := E) (I := I) (G := G) g
  have he : (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) : G → E) =ᶠ[
      𝓝 (nativeLieExponential (I := I) (G := G) v)]
      nativeLieExponentialLocalLogAt (E := E) (I := I) (G := G) v := by
    filter_upwards [nativeLieExponentialLocalLogAt_right (I := I) (G := G) v] with g hg
    apply nativeLieExponential_injective (E := E) (I := I) (G := G)
    exact (nativeLieExponential_globalLogarithm (E := E) (I := I) (G := G) g).trans hg.symm
  exact (nativeLieExponentialLocalLogAt_contMDiffAt (I := I) (G := G) v).congr_of_eventuallyEq he

noncomputable def nativeLieExponentialDiffeomorph : Diffeomorph 𝓘(ℝ, E) I E G ∞ where
  toFun v := nativeLieExponential (I := I) (G := G) v
  invFun := nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
  left_inv := nativeLieGlobalLogarithm_exponential (E := E) (I := I) (G := G)
  right_inv := nativeLieExponential_globalLogarithm (E := E) (I := I) (G := G)
  contMDiff_toFun := nativeLieExponential_contMDiff (I := I) (G := G)
  contMDiff_invFun := nativeLieGlobalLogarithm_contMDiff (E := E) (I := I) (G := G)

 theorem nativeLieGlobalLogarithm_mfderiv (v : E) :
    let exp : E → G := fun z => nativeLieExponential (I := I) (G := G) z
    let D : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I exp v
    let L : E →L[ℝ] E := mfderiv I 𝓘(ℝ, E)
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) : G → E) (exp v)
    L.comp D = ContinuousLinearMap.id ℝ E := by
  let exp : E → G := fun z => nativeLieExponential (I := I) (G := G) z
  let log : G → E := nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
  have he : log ∘ exp = id := funext (nativeLieGlobalLogarithm_exponential (I := I) (G := G))
  have hd : MDifferentiableAt 𝓘(ℝ, E) I exp v :=
    (nativeLieExponential_contMDiff (I := I) (G := G)).mdifferentiableAt (by norm_num)
  have hl : MDifferentiableAt I 𝓘(ℝ, E) log (exp v) :=
    (nativeLieGlobalLogarithm_contMDiff (I := I) (G := G)).mdifferentiableAt (by norm_num)
  have h := mfderiv_comp v hl hd
  rw [he, mfderiv_id] at h
  exact h.symm

end Hindman168
