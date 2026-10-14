import Hindman168.NativeLieAdjointLayer
import Hindman168.NilpotentLinearDeterminant

/-! Genuine unipotency and unit determinant of the ORIGINAL adjoint,
deduced from its actual lowering action on the original lower-central series. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_lie_adjoint_sub_one_pow_layer (g : G) {v : E} {j : ℕ}
    (hv : v ∈ nativeLieLowerCentralModel (I := I) (G := G) j) (k : ℕ) :
    (((nativeLieAdjoint (I := I) g : E →L[ℝ] E)-1)^k) v ∈
      nativeLieLowerCentralModel (I := I) (G := G) (j+k) := by
  induction k with
  | zero => simpa only [pow_zero, one_apply_eq_self, Nat.add_zero] using hv
  | succ k ih =>
    rw [pow_succ']
    change nativeLieAdjoint (I := I) g
      ((((nativeLieAdjoint (I := I) g : E →L[ℝ] E)-1)^k) v) -
        ((((nativeLieAdjoint (I := I) g : E →L[ℝ] E)-1)^k) v) ∈ _
    simpa only [Nat.add_succ] using nativeLieAdjoint_sub_mem_lowerCentral_next (I := I) g ih

theorem native_lie_adjoint_sub_one_pow_zero (g : G) :
    ((nativeLieAdjoint (I := I) g : E →L[ℝ] E)-1)^(Group.nilpotencyClass G) = 0 := by
  ext v
  have hv : v ∈ nativeLieLowerCentralModel (I := I) (G := G) 0 := by
    rw [nativeLieLowerCentralModel_zero]
    trivial
  have h := native_lie_adjoint_sub_one_pow_layer (I := I) g hv (Group.nilpotencyClass G)
  rw [Nat.zero_add, nativeLieLowerCentralModel_nilpotencyClass_bot] at h
  change (((nativeLieAdjoint (I := I) g : E →L[ℝ] E)-1)^(Group.nilpotencyClass G)) v = 0
  exact h

theorem native_lie_adjoint_sub_one_linear_nilpotent (g : G) :
    IsNilpotent ((nativeLieAdjoint (I := I) g).toLinearMap-1) := by
  change IsNilpotent (ContinuousLinearMap.toLinearMapRingHom
    ((nativeLieAdjoint (I := I) g : E →L[ℝ] E)-1))
  exact (show IsNilpotent ((nativeLieAdjoint (I := I) g : E →L[ℝ] E)-1) from
    ⟨Group.nilpotencyClass G, native_lie_adjoint_sub_one_pow_zero (I := I) g⟩).map
      ContinuousLinearMap.toLinearMapRingHom

theorem native_lie_adjoint_determinant_one (g : G) :
    LinearMap.det (nativeLieAdjoint (I := I) g).toLinearMap = 1 := by
  have h := nilpotent_linear_det_one_add ((nativeLieAdjoint (I := I) g).toLinearMap-1)
    (native_lie_adjoint_sub_one_linear_nilpotent (I := I) g)
  have he : (1 : Module.End ℝ E)+((nativeLieAdjoint (I := I) g).toLinearMap-1) =
      (nativeLieAdjoint (I := I) g).toLinearMap := by abel
  rwa [he] at h

end Hindman168
