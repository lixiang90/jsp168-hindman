import Hindman168.NativeProductLieSubgroup

/-! The model of the integrated product subalgebra is exactly its
original coefficient subspace in the product tangent model. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {G K : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  [Group K] [TopologicalSpace K] [ChartedSpace H' K]
  [LieGroup I ∞ G] [LieGroup J ∞ K] [BoundarylessManifold I G]
  [BoundarylessManifold J K] [T2Space G] [T2Space K]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeProductLieModel
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G × GroupLieAlgebra J K)) :
    Submodule ℝ (E × F) := S.toSubmodule

theorem nativeProductLieModel_map_eq
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G × GroupLieAlgebra J K)) :
    nativeLieSubalgebraModel
        (S.map (nativeProductLieEquiv (I := I) (J := J)).symm.toLieHom) =
      nativeProductLieModel S := by
  ext v
  change (show GroupLieAlgebra (I.prod J) (G × K) from v) ∈
      S.map (nativeProductLieEquiv (I := I) (J := J)).symm.toLieHom ↔
    (show GroupLieAlgebra I G × GroupLieAlgebra J K from v) ∈ S
  rw [LieSubalgebra.mem_map]
  constructor
  · rintro ⟨w, hw, h⟩
    change (w.1, w.2) = v at h
    exact (congrArg (fun z : GroupLieAlgebra I G × GroupLieAlgebra J K => z ∈ S) h).mp hw
  · intro hv
    exact ⟨(v.1, v.2), hv, rfl⟩

end Hindman168
