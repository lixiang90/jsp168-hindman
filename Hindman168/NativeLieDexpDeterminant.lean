import Hindman168.NativeLieDexpDefectFiltration
import Hindman168.NilpotentLinearDeterminant

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E]

attribute [local instance] lieGroup_smooth_min_three

omit [FiniteDimensional ℝ E] in
theorem native_lie_dexp_sub_one_nilpotent (v : E) :
    IsNilpotent ((nativeLieDexp (I := I) (G := G) v).toLinearMap-1) := by
  have hW : IsNilpotent (nativeLieDexpDefect (I := I) (G := G) v) :=
    ⟨Group.nilpotencyClass G, nativeLieDexpDefect_pow_nilpotencyClass v⟩
  have he : -(nativeLieDexpDefect (I := I) (G := G) v) =
      nativeLieDexp (I := I) (G := G) v-1 := by
    unfold nativeLieDexpDefect
    abel
  change IsNilpotent (ContinuousLinearMap.toLinearMapRingHom
    (nativeLieDexp (I := I) (G := G) v-1))
  rw [← he]
  exact hW.neg.map ContinuousLinearMap.toLinearMapRingHom

theorem native_lie_dexp_determinant_one (v : E) :
    LinearMap.det (nativeLieDexp (I := I) (G := G) v).toLinearMap = 1 := by
  have h := nilpotent_linear_det_one_add ((nativeLieDexp (I := I) (G := G) v).toLinearMap-1)
    (native_lie_dexp_sub_one_nilpotent (I := I) v)
  have he : (1 : Module.End ℝ E)+((nativeLieDexp (I := I) (G := G) v).toLinearMap-1) =
      (nativeLieDexp (I := I) (G := G) v).toLinearMap := by abel
  rwa [he] at h

theorem native_lie_dexp_finite_inverse_determinant_one (v : E) :
    LinearMap.det (nativeLieDexpFiniteInverse (I := I) (G := G) v).toLinearMap = 1 := by
  have hm : LinearMap.det ((nativeLieDexpFiniteInverse (I := I) (G := G) v).toLinearMap *
      (nativeLieDexp (I := I) (G := G) v).toLinearMap) = 1 := by
    change LinearMap.det ((nativeLieDexpFiniteInverse (I := I) (G := G) v *
      nativeLieDexp (I := I) (G := G) v).toLinearMap) = 1
    rw [nativeLieDexp_finiteInverse_mul]
    exact map_one _
  rwa [map_mul, native_lie_dexp_determinant_one, mul_one] at hm

end Hindman168
