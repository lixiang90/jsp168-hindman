import Hindman168.NativeRationalCubeLieEmbedding
import Hindman168.NativeFiniteProductRationalSpan

/-! The embedded cube algebra is rational for the actual original product
lattice, not merely for an abstract coordinate rational structure. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] nativeFiniteProductTopologicalSpace nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace
  nativeFiniteProductChartTopology nativeFiniteProductChartedSpace
  nativeFiniteProductLieGroup nativeFiniteProductBoundaryless lieGroup_smooth_min_three

attribute [local instance] pointwiseLieRing pointwiseLieAlgebra

attribute [local instance] nativeFiniteProductRationalModule


theorem native_rational_cube_subtype_rational_span {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ) (d : ℕ) :
    Submodule.span ℝ {x : nativeRationalCubeLieAlgebra D F d |
      ∀ V, x.val V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ} = ⊤ := by
  apply (Submodule.span_val_image_eq_iff (upperFaceLieLayer
    (L := GroupLieAlgebra D.I D.G) F.layer d 0) _).mp
  have he : Subtype.val '' {x : nativeRationalCubeLieAlgebra D F d |
      ∀ V, x.val V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ} =
      {z : Finset (Fin d) → GroupLieAlgebra D.I D.G |
        z ∈ upperFaceLieLayer (L := GroupLieAlgebra D.I D.G) F.layer d 0 ∧
        ∀ V, z V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ} := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩; exact ⟨x.property,hx⟩
    · rintro ⟨hz,hq⟩; exact ⟨⟨z,hz⟩,hq,rfl⟩
  exact (congrArg (Submodule.span ℝ) he).trans
    (native_rational_cube_lie_layer_rational_span D F d 0)

theorem native_rational_cube_embedding_rational {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    letI := nativeFiniteProductSimplyConnected (I := D.I) (G := D.G) n
    nativeLatticeRationalSubspace (E := nativeFiniteProduct D.E n)
      (I := nativeFiniteProductCorners D.I n) (nativeFiniteProductLattice D.Γ n)
      (nativeRationalCubeLieEmbedding D F d n e).toLinearMap.range := by
  letI := nativeFiniteProductSimplyConnected (I := D.I) (G := D.G) n
  let f := (nativeRationalCubeLieEmbedding D F d n e).toLinearMap
  change Submodule.span ℝ {w | w ∈ f.range ∧ w ∈
    nativeSubgroupRationalLogSpan (E := nativeFiniteProduct D.E n)
      (I := nativeFiniteProductCorners D.I n) (nativeFiniteProductLattice D.Γ n)} = f.range
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun _ hw => hw.1)
  · rintro w ⟨x,rfl⟩
    have hx : x ∈ Submodule.span ℝ {x : nativeRationalCubeLieAlgebra D F d |
        ∀ V, x.val V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ} := by
      rw [native_rational_cube_subtype_rational_span]
      trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      apply Submodule.subset_span
      refine ⟨⟨y,rfl⟩,?_⟩
      apply native_finite_product_rational_span_mem D n (f y)
      intro k
      change nativeFiniteProductCoordinate n (nativeRationalCubeLieEmbedding D F d n e y) k ∈ _
      rw [native_rational_cube_embedding_coordinate]
      exact hy (e k)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

end Hindman168
