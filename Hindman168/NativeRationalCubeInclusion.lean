import Hindman168.NativeRationalCubeData
import Hindman168.NativeLieSubalgebraNativeCoordinates

/-! Actual native subgroup inclusion and its exact differential. -/
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

@[reducible]
def nativeFiniteProductModelTopology {E : Type*} [NormedAddCommGroup E] (n : ℕ) :
    TopologicalSpace (nativeFiniteProduct E n) :=
  (nativeFiniteProductNormedAddCommGroup (E := E) n).toUniformSpace.toTopologicalSpace

attribute [local instance] nativeFiniteProductModelTopology

noncomputable def nativeRationalCubeGroupInclusion {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    (nativeRationalCubeData D F d n e).G →* nativeFiniteProduct D.G n :=
  (nativeRationalCubeSubgroup D F d n e).subtype

noncomputable def nativeRationalCubeModelInclusion {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    (nativeRationalCubeData D F d n e).E →L[ℝ] nativeFiniteProduct D.E n :=
  (nativeLieSubalgebraModel (E := nativeFiniteProduct D.E n)
    (nativeRationalCubeNativeAlgebra D F d n e)).subtype.toContinuousLinearMap

theorem native_rational_cube_inclusion_contMDiff {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    ContMDiff (nativeRationalCubeData D F d n e).I (nativeFiniteProductCorners D.I n) ∞
      (nativeRationalCubeGroupInclusion D F d n e) := by
  letI := nativeFiniteProductSimplyConnected (I := D.I) (G := D.G) n
  exact nativeLieSubalgebra_inclusion_contMDiff (nativeRationalCubeNativeAlgebra D F d n e)

theorem native_rational_cube_inclusion_mfderiv {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    mfderiv (nativeRationalCubeData D F d n e).I (nativeFiniteProductCorners D.I n)
      (nativeRationalCubeGroupInclusion D F d n e) 1 = nativeRationalCubeModelInclusion D F d n e := by
  letI := nativeFiniteProductSimplyConnected (I := D.I) (G := D.G) n
  exact nativeLieSubalgebra_inclusion_mfderiv (nativeRationalCubeNativeAlgebra D F d n e)

theorem native_rational_cube_data_exponential {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (v : (nativeRationalCubeData D F d n e).E) :
    nativeRationalCubeGroupInclusion D F d n e
      (nativeLieExponential (I := (nativeRationalCubeData D F d n e).I)
        (G := (nativeRationalCubeData D F d n e).G) v) =
      nativeLieExponential (I := nativeFiniteProductCorners D.I n)
        (G := nativeFiniteProduct D.G n) (nativeRationalCubeModelInclusion D F d n e v) := by
  have h := nativeLieExponential_map (I := (nativeRationalCubeData D F d n e).I)
    (J := nativeFiniteProductCorners D.I n) (nativeRationalCubeGroupInclusion D F d n e)
    ((native_rational_cube_inclusion_contMDiff D F d n e).mdifferentiable (by norm_num)) v
  rw [native_rational_cube_inclusion_mfderiv] at h
  exact h

theorem native_rational_cube_inclusion_adjoint {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (v w : (nativeRationalCubeData D F d n e).E) :
    nativeRationalCubeModelInclusion D F d n e
      (nativeLieAdjointDifferential (I := (nativeRationalCubeData D F d n e).I)
        (G := (nativeRationalCubeData D F d n e).G) v w) =
      nativeLieAdjointDifferential (I := nativeFiniteProductCorners D.I n)
        (G := nativeFiniteProduct D.G n) (nativeRationalCubeModelInclusion D F d n e v)
          (nativeRationalCubeModelInclusion D F d n e w) := by
  have h := nativeSmoothHom_generator_intertwine
    (I := (nativeRationalCubeData D F d n e).I) (J := nativeFiniteProductCorners D.I n)
    (nativeRationalCubeGroupInclusion D F d n e) (native_rational_cube_inclusion_contMDiff D F d n e) v w
  rw [native_rational_cube_inclusion_mfderiv] at h
  simpa only [nativeLieAdjointGenerator_eq_differential] using h

end Hindman168
