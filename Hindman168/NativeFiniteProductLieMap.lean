import Hindman168.NativeFiniteProductCoordinates

/-! A finite family of original Lie evaluation homomorphisms gives a
genuine Lie homomorphism into the native Lie algebra of the actual finite
product group. Its coordinates are exactly the supplied evaluations. -/

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
  {A : Type*} [LieRing A] [LieAlgebra ℝ A]

noncomputable def nativeFiniteProductLieMap : (n : ℕ) →
    (Fin (n + 1) → A →ₗ⁅ℝ⁆ GroupLieAlgebra I G) →
      A →ₗ⁅ℝ⁆ GroupLieAlgebra (nativeFiniteProductCorners I n) (nativeFiniteProduct G n)
  | 0, f => f 0
  | n + 1, f =>
    (nativeProductLieEquiv (I := nativeFiniteProductCorners I n) (J := I)
      (G := nativeFiniteProduct G n) (K := G)).symm.toLieHom.comp
        ((nativeFiniteProductLieMap n (fun i => f i.castSucc)).prod (f (Fin.last (n + 1))))

theorem nativeFiniteProductLieMap_coordinate (n : ℕ)
    (f : Fin (n + 1) → A →ₗ⁅ℝ⁆ GroupLieAlgebra I G) (x : A) (i : Fin (n + 1)) :
    (show GroupLieAlgebra I G from
      nativeFiniteProductCoordinate n (nativeFiniteProductLieMap n f x) i) = f i x := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  | succ n ih =>
    refine Fin.lastCases ?_ ?_ i
    · simp only [nativeFiniteProductCoordinate_last]
      rfl
    · intro j
      simp only [nativeFiniteProductCoordinate_castSucc]
      exact ih (fun k => f k.castSucc) j

theorem nativeFiniteProductLieMap_injective (n : ℕ)
    (f : Fin (n + 1) → A →ₗ⁅ℝ⁆ GroupLieAlgebra I G)
    (h : Function.Injective (fun x => fun i => f i x)) :
    Function.Injective (nativeFiniteProductLieMap n f) := by
  intro x y hxy
  apply h
  funext i
  have hi := congrArg (fun z => nativeFiniteProductCoordinate n z i) hxy
  exact (nativeFiniteProductLieMap_coordinate n f x i).symm.trans
    (hi.trans (nativeFiniteProductLieMap_coordinate n f y i))

end Hindman168
