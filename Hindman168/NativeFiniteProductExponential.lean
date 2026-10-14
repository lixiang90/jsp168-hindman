import Hindman168.NativeFiniteProductLieMap

/-! Every original coordinate of the genuine finite product exponential
is the original group exponential. Global logarithms have the same exact
coordinate compatibility, derived from those original inverse laws. -/

namespace Hindman168
open scoped Manifold ContDiff

attribute [local instance] nativeFiniteProductTopologicalSpace nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace
  nativeFiniteProductChartTopology nativeFiniteProductChartedSpace
  nativeFiniteProductLieGroup nativeFiniteProductBoundaryless lieGroup_smooth_min_three

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

theorem nativeFiniteProductExponential_coordinate (n : ℕ)
    (v : GroupLieAlgebra (nativeFiniteProductCorners I n) (nativeFiniteProduct G n))
    (i : Fin (n + 1)) :
    nativeFiniteProductCoordinate n
        (nativeLieExponential (I := nativeFiniteProductCorners I n)
          (G := nativeFiniteProduct G n) v) i =
      nativeLieExponential (I := I) (G := G) (nativeFiniteProductCoordinate n v i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ ?_ i
    · simp only [nativeFiniteProductCoordinate_last]
      exact nativeProductExponential_snd (I := nativeFiniteProductCorners I n) (J := I)
        (G := nativeFiniteProduct G n) (K := G) v
    · intro j
      have h := nativeProductExponential_fst (I := nativeFiniteProductCorners I n) (J := I)
        (G := nativeFiniteProduct G n) (K := G) v
      simp only [nativeFiniteProductCoordinate_castSucc]
      exact (congrArg (fun g => nativeFiniteProductCoordinate n g j) h).trans
        (ih (show GroupLieAlgebra (nativeFiniteProductCorners I n)
          (nativeFiniteProduct G n) from v.1) j)

theorem nativeFiniteProductLieMap_exponential_coordinate {A : Type*}
    [LieRing A] [LieAlgebra ℝ A] (n : ℕ)
    (f : Fin (n + 1) → A →ₗ⁅ℝ⁆ GroupLieAlgebra I G) (x : A) (i : Fin (n + 1)) :
    nativeFiniteProductCoordinate n
        (nativeLieExponential (I := nativeFiniteProductCorners I n)
          (G := nativeFiniteProduct G n) (nativeFiniteProductLieMap n f x)) i =
      nativeLieExponential (I := I) (G := G) (f i x) :=
  (nativeFiniteProductExponential_coordinate n (nativeFiniteProductLieMap n f x) i).trans
    (congrArg (nativeLieExponential (I := I) (G := G))
      (nativeFiniteProductLieMap_coordinate n f x i))

variable [FiniteDimensional ℝ E] [Group.IsNilpotent G]
  [ConnectedSpace G] [SimplyConnectedSpace G]

theorem nativeFiniteProductGlobalLogarithm_coordinate (n : ℕ)
    (g : nativeFiniteProduct G n) (i : Fin (n + 1)) :
    letI := nativeFiniteProductSimplyConnected (I := I) (G := G) n
    (show GroupLieAlgebra I G from nativeFiniteProductCoordinate n
      (nativeLieGlobalLogarithm (I := nativeFiniteProductCorners I n)
        (G := nativeFiniteProduct G n) g) i) =
      nativeLieGlobalLogarithm (I := I) (G := G) (nativeFiniteProductCoordinate n g i) := by
  letI := nativeFiniteProductSimplyConnected (I := I) (G := G) n
  apply nativeLieExponential_injective (I := I) (G := G)
  exact (nativeFiniteProductExponential_coordinate n
      (nativeLieGlobalLogarithm (I := nativeFiniteProductCorners I n)
        (G := nativeFiniteProduct G n) g) i).symm.trans
    ((congrArg (fun z : nativeFiniteProduct G n => nativeFiniteProductCoordinate n z i)
      (nativeLieExponential_globalLogarithm (I := nativeFiniteProductCorners I n)
        (G := nativeFiniteProduct G n) g)).trans
      (nativeLieExponential_globalLogarithm (I := I) (G := G)
        (nativeFiniteProductCoordinate n g i)).symm)

end Hindman168
