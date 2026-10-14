import Hindman168.NativeRationalCubeFaceInclusion
import Hindman168.UpperFaceLieVertexDetection
import Hindman168.UpperFaceGroupVertexElimination

/-! The native exponential cube subgroup has EXACTLY the paper's
upper-face generated vertex arrays, for the SAME final filtration. -/
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



theorem native_rational_cube_vertex_layer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (z : Finset (Fin d) → D.G)
    (hz : z ∈ (nativeRationalCubeSubgroup D F d n e).map (nativeCubeVertexHom d n e))
    (V : Finset (Fin d)) (hzero : ∀ U, U ⊂ V → z U = 1) :
    z V ∈ nativeRationalSubgroupLayer D F V.card := by
  obtain ⟨g,hg,rfl⟩ := hz
  obtain ⟨x,hx⟩ := (native_rational_cube_subgroup_mem_iff D F d n e g).mp hg
  have hc (U : Finset (Fin d)) : nativeCubeVertexHom d n e g U =
      nativeLieExponential (I := D.I) (G := D.G) (x.val U) := by
    have hu := hx (e.symm U)
    exact hu.trans (congrArg (fun V => nativeLieExponential (I := D.I) (G := D.G) (x.val V))
      (e.apply_symm_apply U))
  have hlogzero (U : Finset (Fin d)) (hU : U ⊂ V) : x.val U = 0 := by
    apply nativeLieExponential_injective (E := D.E) (I := D.I) (G := D.G)
    exact (hc U).symm.trans ((hzero U hU).trans (nativeLieExponential_zero (I := D.I) (G := D.G)).symm)
  have hmem := upper_face_lie_vertex_layer (L := GroupLieAlgebra D.I D.G)
    F.layer x.val x.property V hlogzero
  rw [hc V]
  exact native_rational_subgroup_layer_exp_mem D F V.card hmem

theorem native_rational_cube_group_identification {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    (nativeRationalCubeSubgroup D F d n e).map (nativeCubeVertexHom d n e) =
      upperFaceCubeGroup (nativeRationalSubgroupLayer D F) d := by
  apply upper_face_group_eq_of_vertex_layers
  · exact fun A g hg => native_rational_cube_face_mem D F d n e A g hg
  · exact fun z hz V hzero => native_rational_cube_vertex_layer D F d n e z hz V hzero

end Hindman168
