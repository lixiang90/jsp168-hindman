import Hindman168.NativeCubeAmbientLayers

/-! EVERY ambient cube layer is rational for the ACTUAL product lattice. -/
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


attribute [local instance] nativeFiniteProduct_topologicalGroup

theorem native_cube_ambient_layer_rational {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (i : ℕ) :
    letI := nativeFiniteProductSimplyConnected (I := D.I) (G := D.G) n
    nativeLatticeRationalSubspace (E := nativeFiniteProduct D.E n)
      (I := nativeFiniteProductCorners D.I n) (nativeFiniteProductLattice D.Γ n)
      (nativeCubeAmbientLayer D F d n e i) := by
  letI := nativeFiniteProductSimplyConnected (I := D.I) (G := D.G) n
  let f := (nativeCubeArrayEmbedding D d n e).toLinearMap
  change Submodule.span ℝ {v | v ∈ nativeCubeAmbientLayer D F d n e i ∧ v ∈
    nativeSubgroupRationalLogSpan (E := nativeFiniteProduct D.E n)
      (I := nativeFiniteProductCorners D.I n) (nativeFiniteProductLattice D.Γ n)} = _
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun _ hv => hv.1)
  · rintro v ⟨x,hx,rfl⟩
    have hx' : x ∈ Submodule.span ℝ {z : Finset (Fin d) → GroupLieAlgebra D.I D.G |
        z ∈ upperFaceLieLayer (L := GroupLieAlgebra D.I D.G) F.layer d i ∧
        ∀ V, z V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ} :=
      (native_rational_cube_lie_layer_rational_span D F d i).symm ▸ hx
    clear hx
    change f x ∈ _
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      apply Submodule.subset_span
      refine ⟨⟨y,hy.1,rfl⟩,?_⟩
      apply native_finite_product_rational_span_mem D n (f y)
      intro k
      exact (native_cube_array_embedding_coordinate D d n e y k).symm ▸ hy.2 (e k)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

end Hindman168
