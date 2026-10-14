import Hindman168.NativeProductLieTopology

/-! The actual graph Lie subalgebra of a Lie homomorphism integrates
inside the actual product of the original groups. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {G K : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  [Group K] [TopologicalSpace K] [ChartedSpace H' K]
  [LieGroup I ∞ G] [LieGroup J ∞ K] [BoundarylessManifold I G]
  [BoundarylessManifold J K] [T2Space G] [T2Space K]
  [Group.IsNilpotent G] [Group.IsNilpotent K]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieSubalgebraGraph
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (φ : S →ₗ⁅ℝ⁆ GroupLieAlgebra J K) :
    LieSubalgebra ℝ (GroupLieAlgebra I G × GroupLieAlgebra J K) := (S.incl.prod φ).range

noncomputable def nativeLieSubalgebraGraphSubgroup
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (φ : S →ₗ⁅ℝ⁆ GroupLieAlgebra J K) :
    Subgroup (G × K) :=
  nativeProductLieSubgroup (E := E) (F := F) (I := I) (J := J) (G := G) (K := K)
    (nativeLieSubalgebraGraph S φ)

theorem nativeLieSubalgebraGraphSubgroup_mem_iff
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (φ : S →ₗ⁅ℝ⁆ GroupLieAlgebra J K)
    (g : G × K) :
    g ∈ nativeLieSubalgebraGraphSubgroup (E := E) (F := F) S φ ↔
      ∃ v : S, (nativeLieExponential (I := I) (G := G) v.val,
        nativeLieExponential (I := J) (G := K) (φ v)) = g := by
  unfold nativeLieSubalgebraGraphSubgroup
  rw [nativeProductLieSubgroup_mem_iff]
  constructor
  · rintro ⟨w, hw, hg⟩
    obtain ⟨v, hv⟩ := (LieHom.mem_range (S.incl.prod φ) w).mp hw
    exact ⟨v, (congrArg (fun z : GroupLieAlgebra I G × GroupLieAlgebra J K =>
      (nativeLieExponential (I := I) (G := G) z.1,
        nativeLieExponential (I := J) (G := K) z.2)) hv).trans hg⟩
  · rintro ⟨v, hv⟩
    exact ⟨_, (S.incl.prod φ).mem_range_self v, hv⟩

theorem nativeLieSubalgebraGraphSubgroup_fst_mem
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (φ : S →ₗ⁅ℝ⁆ GroupLieAlgebra J K)
    (g : G × K) (hg : g ∈ nativeLieSubalgebraGraphSubgroup (E := E) (F := F) S φ) :
    g.1 ∈ nativeLieSubalgebraSubgroup (E := E) S := by
  obtain ⟨v, hv⟩ := (nativeLieSubalgebraGraphSubgroup_mem_iff S φ g).mp hg
  exact ⟨v.val, v.property, congrArg Prod.fst hv⟩

end Hindman168
