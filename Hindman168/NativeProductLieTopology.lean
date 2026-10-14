import Hindman168.NativeProductLieModel

/-! The literal pair of original exponentials identifies the original
coefficient subspace with the integrated subgroup, with its inherited
topology. Its inverse is the literal pair of original global logarithms. -/

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
  [ConnectedSpace G] [SimplyConnectedSpace G]
  [ConnectedSpace K] [SimplyConnectedSpace K]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeProductLieExponentialHomeomorph
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G × GroupLieAlgebra J K)) :
    nativeProductLieModel S ≃ₜ nativeProductLieSubgroup S where
  toFun v := ⟨(nativeLieExponential (I := I) (G := G) v.val.1,
    nativeLieExponential (I := J) (G := K) v.val.2),
    (nativeProductLieSubgroup_mem_iff S _).mpr ⟨_, v.property, rfl⟩⟩
  invFun g := ⟨(nativeLieGlobalLogarithm (I := I) (G := G) g.val.1,
    nativeLieGlobalLogarithm (I := J) (G := K) g.val.2),
    (nativeProductLieSubgroup_globalLogarithm_iff S g.val).mp g.property⟩
  left_inv v := Subtype.ext (Prod.ext
    (nativeLieGlobalLogarithm_exponential (I := I) (G := G) v.val.1)
    (nativeLieGlobalLogarithm_exponential (I := J) (G := K) v.val.2))
  right_inv g := Subtype.ext (Prod.ext
    (nativeLieExponential_globalLogarithm (I := I) (G := G) g.val.1)
    (nativeLieExponential_globalLogarithm (I := J) (G := K) g.val.2))
  continuous_toFun :=
    (((nativeLieExponential_contMDiff (I := I) (G := G)).continuous.comp
      (continuous_fst.comp continuous_subtype_val)).prodMk
    ((nativeLieExponential_contMDiff (I := J) (G := K)).continuous.comp
      (continuous_snd.comp continuous_subtype_val))).subtype_mk _
  continuous_invFun :=
    (((nativeLieGlobalLogarithm (I := I) (G := G)).continuous.comp
      (continuous_fst.comp continuous_subtype_val)).prodMk
    ((nativeLieGlobalLogarithm (I := J) (G := K)).continuous.comp
      (continuous_snd.comp continuous_subtype_val))).subtype_mk _

theorem nativeProductLieExponentialHomeomorph_apply
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G × GroupLieAlgebra J K))
    (v : nativeProductLieModel S) :
    (nativeProductLieExponentialHomeomorph S v).val =
      (nativeLieExponential (I := I) (G := G) v.val.1,
        nativeLieExponential (I := J) (G := K) v.val.2) := rfl

theorem nativeProductLieSubgroup_contractible
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G × GroupLieAlgebra J K)) :
    ContractibleSpace (nativeProductLieSubgroup S) := by
  let V : Submodule ℝ (E × F) := nativeProductLieModel S
  letI : ContractibleSpace V := V.convex.contractibleSpace ⟨0, V.zero_mem⟩
  exact (nativeProductLieExponentialHomeomorph S).symm.contractibleSpace

theorem nativeProductLieSubgroup_connected
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G × GroupLieAlgebra J K)) :
    ConnectedSpace (nativeProductLieSubgroup S) := by
  letI := nativeProductLieSubgroup_contractible S
  infer_instance

end Hindman168
