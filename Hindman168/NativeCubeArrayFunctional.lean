import Hindman168.NativeResidueCubeData
import Hindman168.FiniteRealSubmoduleRetraction

/-! An actual native cube functional extends to full vertex Lie arrays.
Its restriction agrees through a constructed surjection onto the native
cube model; no functional, coordinate, or bracket oracle is supplied. -/
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

noncomputable def nativeCubeLieModelMap {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    nativeRationalCubeLieAlgebra D F d →ₗ[ℝ] (nativeRationalCubeData D F d n e).E :=
  (nativeRationalCubeLieEmbedding D F d n e).toLinearMap.codRestrict
    (nativeLieSubalgebraModel (E := nativeFiniteProduct D.E n) (nativeRationalCubeNativeAlgebra D F d n e))
    (fun x => ⟨x,rfl⟩)

theorem native_cube_lie_model_map_surjective {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    Function.Surjective (nativeCubeLieModelMap D F d n e) := by
  intro v
  obtain ⟨x,hx⟩ := v.property
  exact ⟨x,Subtype.ext hx⟩

noncomputable def nativeCubeArrayFunctional {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (chi : (nativeRationalCubeData D F d n e).E →ₗ[ℝ] ℝ) :
    (Finset (Fin d) → GroupLieAlgebra D.I D.G) →ₗ[ℝ] ℝ :=
  chi.comp ((finiteRealSubmoduleRetraction
    (nativeLieSubalgebraModel (E := nativeFiniteProduct D.E n)
      (nativeRationalCubeNativeAlgebra D F d n e))).toLinearMap.comp
    (nativeCubeArrayEmbedding D d n e).toLinearMap)

theorem native_cube_array_functional_agrees {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (chi : (nativeRationalCubeData D F d n e).E →ₗ[ℝ] ℝ)
    (x : nativeRationalCubeLieAlgebra D F d) :
    nativeCubeArrayFunctional D F d n e chi x.val = chi (nativeCubeLieModelMap D F d n e x) := by
  apply congrArg chi
  exact (congrArg (finiteRealSubmoduleRetraction
      (nativeLieSubalgebraModel (E := nativeFiniteProduct D.E n) (nativeRationalCubeNativeAlgebra D F d n e)))
    (native_cube_array_embedding_restrict D F d n e x)).trans
      (finiteRealSubmoduleRetraction_left _ (nativeCubeLieModelMap D F d n e x))

theorem native_cube_array_functional_nonzero {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (chi : (nativeRationalCubeData D F d n e).E →ₗ[ℝ] ℝ) (hchi : chi ≠ 0) :
    ∃ z ∈ upperFaceLieLayer (L := GroupLieAlgebra D.I D.G) F.layer d 0,
      nativeCubeArrayFunctional D F d n e chi z ≠ 0 := by
  obtain ⟨v,hv⟩ := DFunLike.ne_iff.mp hchi
  obtain ⟨x,rfl⟩ := native_cube_lie_model_map_surjective D F d n e v
  refine ⟨x.val,x.property,?_⟩
  exact fun hz => hv ((native_cube_array_functional_agrees D F d n e chi x).symm.trans hz)

theorem native_cube_lie_model_bracket {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (x y : nativeRationalCubeLieAlgebra D F d) :
    nativeCubeLieModelMap D F d n e ⁅x,y⁆ =
      nativeLieAdjointDifferential (I := (nativeRationalCubeData D F d n e).I)
        (G := (nativeRationalCubeData D F d n e).G)
        (nativeCubeLieModelMap D F d n e x) (nativeCubeLieModelMap D F d n e y) := by
  apply Subtype.ext
  have hMap := (nativeRationalCubeLieEmbedding D F d n e).map_lie x y
  have hAmbient := (nativeLieAdjointGenerator_eq_native_bracket
    (I := nativeFiniteProductCorners D.I n) (G := nativeFiniteProduct D.G n)
      (nativeRationalCubeLieEmbedding D F d n e x) (nativeRationalCubeLieEmbedding D F d n e y)).symm.trans
    (DFunLike.congr_fun (nativeLieAdjointGenerator_eq_differential
      (I := nativeFiniteProductCorners D.I n) (G := nativeFiniteProduct D.G n) _) _)
  exact (hMap.trans hAmbient).trans
    (native_rational_cube_inclusion_adjoint D F d n e
      (nativeCubeLieModelMap D F d n e x) (nativeCubeLieModelMap D F d n e y)).symm

end Hindman168
