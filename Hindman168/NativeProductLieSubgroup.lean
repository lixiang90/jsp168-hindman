import Hindman168.NativeProductGlobalLogarithm

/-! Integrate an actual Lie subalgebra of the product of the original
native Lie algebras inside the original product group. -/

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

noncomputable def nativeProductLieSubgroup
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G × GroupLieAlgebra J K)) :
    Subgroup (G × K) :=
  nativeLieSubalgebraSubgroup (I := I.prod J) (G := G × K)
    (S.map (nativeProductLieEquiv (I := I) (J := J)).symm.toLieHom)

theorem nativeProductLieSubgroup_mem_iff
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G × GroupLieAlgebra J K)) (g : G × K) :
    g ∈ nativeProductLieSubgroup S ↔
      ∃ v : GroupLieAlgebra I G × GroupLieAlgebra J K, v ∈ S ∧
        (nativeLieExponential (I := I) (G := G) v.1,
          nativeLieExponential (I := J) (G := K) v.2) = g := by
  unfold nativeProductLieSubgroup
  rw [nativeLieSubalgebraSubgroup_mem_iff]
  constructor
  · rintro ⟨w, hw, hg⟩
    change w ∈ S.map (nativeProductLieEquiv (I := I) (J := J)).symm.toLieHom at hw
    obtain ⟨v, hv, hvw⟩ :=
      (LieSubalgebra.mem_map (L₂ := GroupLieAlgebra (I.prod J) (G × K)) _ _ _).mp hw
    refine ⟨v, hv, ?_⟩
    change (v.1, v.2) = w at hvw
    rw [← hvw] at hg
    exact (nativeProductExponential_eq (I := I) (J := J) (G := G) (K := K)
      (v.1, v.2)).symm.trans hg
  · rintro ⟨v, hv, hg⟩
    refine ⟨(v.1, v.2), ?_, ?_⟩
    · exact (LieSubalgebra.mem_map
        (L₂ := GroupLieAlgebra (I.prod J) (G × K)) _ _ _).mpr ⟨v, hv, rfl⟩
    · exact (nativeProductExponential_eq (I := I) (J := J) (G := G) (K := K)
        (v.1, v.2)).trans hg

variable [ConnectedSpace G] [SimplyConnectedSpace G]
  [ConnectedSpace K] [SimplyConnectedSpace K]

theorem nativeProductLieSubgroup_globalLogarithm_iff
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G × GroupLieAlgebra J K)) (g : G × K) :
    g ∈ nativeProductLieSubgroup S ↔
      (nativeLieGlobalLogarithm (I := I) (G := G) g.1,
        nativeLieGlobalLogarithm (I := J) (G := K) g.2) ∈ S := by
  rw [nativeProductLieSubgroup_mem_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hp : (show GroupLieAlgebra I G × GroupLieAlgebra J K from
        (nativeLieGlobalLogarithm (I := I) (G := G)
          (nativeLieExponential (I := I) (G := G) v.1),
        nativeLieGlobalLogarithm (I := J) (G := K)
          (nativeLieExponential (I := J) (G := K) v.2))) = v :=
      Prod.ext (nativeLieGlobalLogarithm_exponential (I := I) (G := G) v.1)
        (nativeLieGlobalLogarithm_exponential (I := J) (G := K) v.2)
    exact (congrArg (fun z : GroupLieAlgebra I G × GroupLieAlgebra J K => z ∈ S) hp).mpr hv
  · intro hg
    exact ⟨_, hg, Prod.ext (nativeLieExponential_globalLogarithm (I := I) (G := G) g.1)
      (nativeLieExponential_globalLogarithm (I := J) (G := K) g.2)⟩

theorem nativeProductLieSubgroup_closed
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G × GroupLieAlgebra J K)) :
    IsClosed (nativeProductLieSubgroup S : Set (G × K)) := by
  letI := nativeProductGroup_simplyConnected (I := I) (J := J) (G := G) (K := K)
  exact nativeLieSubalgebraSubgroup_closed
    (S.map (nativeProductLieEquiv (I := I) (J := J)).symm.toLieHom)

theorem nativeProductLieSubgroup_simplyConnected
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G × GroupLieAlgebra J K)) :
    SimplyConnectedSpace (nativeProductLieSubgroup S) := by
  letI := nativeProductGroup_simplyConnected (I := I) (J := J) (G := G) (K := K)
  exact nativeLieSubalgebraSubgroup_simplyConnected
    (S.map (nativeProductLieEquiv (I := I) (J := J)).symm.toLieHom)

end Hindman168
