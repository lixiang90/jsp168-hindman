import Hindman168.NativeLieAdjointDerivative
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! Smoothness of the actual native adjoint as an operator-valued map.
The genuine parameterized derivative theorem applies to original joint
conjugation. Both derivative base points are the actual group identity,
so the native tangent coordinate changes are the identity maps. -/

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G]

 theorem nativeLieAdjoint_contMDiff :
    ContMDiff I 𝓘(ℝ, E →L[ℝ] E) ∞ (nativeLieAdjoint (I := I) : G → E →L[ℝ] E) := by
  intro g₀
  have hf := (nativeLieConjugation_joint_contMDiff (I := I) (G := G)).contMDiffAt
    (x := (g₀, (1 : G)))
  have h := hf.mfderiv (fun g x : G => g * x * g⁻¹) (fun _ : G => (1 : G))
    (contMDiffAt_const : ContMDiffAt I I ∞ (fun _ : G => (1 : G)) g₀)
    (by rw [ENat.coe_top_add_one])
  have heq : inTangentCoordinates I I (fun _ : G => (1 : G))
      (fun g : G => g * (1 : G) * g⁻¹)
      (fun g : G => mfderiv I I (fun x : G => g * x * g⁻¹) (1 : G)) g₀ =
      nativeLieAdjoint (I := I) := by
    funext g
    rw [inTangentCoordinates_eq]
    · simp only [mul_one, mul_inv_cancel]
      apply ContinuousLinearMap.ext
      intro v
      change tangentCoordChange I (1 : G) (1 : G) (1 : G)
        (nativeLieAdjoint (I := I) g (tangentCoordChange I (1 : G) (1 : G) (1 : G) v)) =
          nativeLieAdjoint (I := I) g v
      simp only [tangentCoordChange_self (mem_extChartAt_source (I := I) (1 : G))]
    · exact mem_chart_source H (1 : G)
    · simpa only [mul_one, mul_inv_cancel] using mem_chart_source H (1 : G)
  rw [heq] at h
  exact h

 theorem nativeLieAdjoint_joint_contMDiff :
    ContMDiff (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : G × E => nativeLieAdjoint (I := I) p.1 p.2) :=
  (nativeLieAdjoint_contMDiff (I := I) (G := G)).comp contMDiff_fst |>.clm_apply contMDiff_snd

 theorem nativeLieAdjoint_continuous :
    Continuous (nativeLieAdjoint (I := I) : G → E →L[ℝ] E) :=
  (nativeLieAdjoint_contMDiff (I := I) (G := G)).continuous

end Hindman168
