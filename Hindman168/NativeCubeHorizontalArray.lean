import Hindman168.NativeCubeArrayFunctional
import Hindman168.NativeRationalKernelLieFiltration
import Hindman168.RoughNativeHorizontalCharacterGrid
import Hindman168.RoughNativeCharacterNormalization

/-! Genuine horizontal functionals on the ACTUAL cube nilmanifold
annihilate array brackets and are rational on original rational arrays. -/
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
attribute [local instance] nativeFiniteProductRationalModule nativeFiniteProduct_topologicalGroup
attribute [local instance] nativeFiniteProductModelTopology

theorem native_cube_horizontal_array_bracket {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (chi : (nativeRationalCubeData D F d n e).E →ₗ[ℝ] ℝ)
    (hChi : RoughNativeHorizontalFunctional (I := (nativeRationalCubeData D F d n e).I)
      (nativeRationalCubeData D F d n e).Γ chi) :
    ∀ z ∈ upperFaceLieLayer (L := GroupLieAlgebra D.I D.G) F.layer d 0,
      ∀ w ∈ upperFaceLieLayer (L := GroupLieAlgebra D.I D.G) F.layer d 0,
        nativeCubeArrayFunctional D F d n e chi ⁅z,w⁆ = 0 := by
  intro z hz w hw
  let x : nativeRationalCubeLieAlgebra D F d := ⟨z,hz⟩
  let y : nativeRationalCubeLieAlgebra D F d := ⟨w,hw⟩
  have he := native_cube_array_functional_agrees D F d n e chi ⁅x,y⁆
  have hm := native_cube_lie_model_bracket D F d n e x y
  exact he.trans ((congrArg chi hm).trans
    (hChi.2.1 (native_rational_lie_bracket_mem_commutator (nativeRationalCubeData D F d n e)
      (nativeCubeLieModelMap D F d n e x) (nativeCubeLieModelMap D F d n e y))))

theorem native_cube_lie_model_rational {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (x : nativeRationalCubeLieAlgebra D F d)
    (hx : ∀ V, x.val V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    nativeCubeLieModelMap D F d n e x ∈
      nativeSubgroupRationalLogSpan (E := (nativeRationalCubeData D F d n e).E)
        (I := (nativeRationalCubeData D F d n e).I) (nativeRationalCubeData D F d n e).Γ := by
  letI := nativeFiniteProductSimplyConnected (I := D.I) (G := D.G) n
  apply (native_cube_inclusion_rational_iff D F d n e _).mpr
  apply native_finite_product_rational_span_mem D n
  intro k
  exact (native_rational_cube_embedding_coordinate D F d n e x k).symm ▸ hx (e k)

theorem native_cube_horizontal_array_rational {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (chi : (nativeRationalCubeData D F d n e).E →ₗ[ℝ] ℝ)
    (hChi : RoughNativeHorizontalFunctional (I := (nativeRationalCubeData D F d n e).I)
      (nativeRationalCubeData D F d n e).Γ chi)
    (x : nativeRationalCubeLieAlgebra D F d)
    (hx : ∀ V, x.val V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    ∃ q : ℚ, nativeCubeArrayFunctional D F d n e chi x.val = (q : ℝ) := by
  obtain ⟨q,hq⟩ := rough_native_integral_character_rational_on_span
    (I := (nativeRationalCubeData D F d n e).I) (nativeRationalCubeData D F d n e).Γ chi hChi.2.2
    (nativeCubeLieModelMap D F d n e x) (native_cube_lie_model_rational D F d n e x hx)
  exact ⟨q,(native_cube_array_functional_agrees D F d n e chi x).trans hq⟩

end Hindman168
