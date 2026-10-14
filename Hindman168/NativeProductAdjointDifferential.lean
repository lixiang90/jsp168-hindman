import Hindman168.NativeProductLieAlgebra

/-! The ACTUAL native product adjoint differential has EXACT original
coordinate components, from the proved native product Lie brackets. -/

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

theorem native_product_adjoint_differential (v w : E × F) :
    nativeLieAdjointDifferential (I := I.prod J) (G := G × K) v w =
      (nativeLieAdjointDifferential (I := I) (G := G) v.1 w.1,
        nativeLieAdjointDifferential (I := J) (G := K) v.2 w.2) := by
  let v' : GroupLieAlgebra (I.prod J) (G × K) := v
  let w' : GroupLieAlgebra (I.prod J) (G × K) := w
  have hProd : nativeLieAdjointDifferential (I := I.prod J) (G := G × K) v w =
      (⁅v',w'⁆ : GroupLieAlgebra (I.prod J) (G × K)) :=
    (congrArg (fun A : (E × F) →L[ℝ] (E × F) => A w)
      (nativeLieAdjointGenerator_eq_differential (I := I.prod J) (G := G × K) v)).symm.trans
      (nativeLieAdjointGenerator_eq_native_bracket (I := I.prod J) (G := G × K) v' w')
  have hE : nativeLieAdjointDifferential (I := I) (G := G) v.1 w.1 =
      (⁅(show GroupLieAlgebra I G from v.1),(show GroupLieAlgebra I G from w.1)⁆ : GroupLieAlgebra I G) :=
    (congrArg (fun A : E →L[ℝ] E => A w.1)
      (nativeLieAdjointGenerator_eq_differential (I := I) (G := G) v.1)).symm.trans
      (nativeLieAdjointGenerator_eq_native_bracket (I := I) (G := G) v.1 w.1)
  have hF : nativeLieAdjointDifferential (I := J) (G := K) v.2 w.2 =
      (⁅(show GroupLieAlgebra J K from v.2),(show GroupLieAlgebra J K from w.2)⁆ : GroupLieAlgebra J K) :=
    (congrArg (fun A : F →L[ℝ] F => A w.2)
      (nativeLieAdjointGenerator_eq_differential (I := J) (G := K) v.2)).symm.trans
      (nativeLieAdjointGenerator_eq_native_bracket (I := J) (G := K) v.2 w.2)
  rw [hProd,hE,hF]
  exact Prod.ext (nativeProductLie_bracket_fst v' w') (nativeProductLie_bracket_snd v' w')

end Hindman168
