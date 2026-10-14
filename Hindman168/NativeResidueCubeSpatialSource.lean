import Hindman168.NativeResidueCubeBoundedPolynomial
import Hindman168.RoughVectorSpatialLift
import Hindman168.CubeSpatialTopCoefficient

/-! All original cube variables are spatial in the quantitative box interface.
The new Option parameter is unused; original b0 is spatial coordinate zero. -/
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

open scoped BigOperators

noncomputable def nativeResidueCubeSpatialPolynomial {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) :
    RoughVectorMvPolynomial (Option (Fin (d+1))) (nativeResidueCubeData D F ρ hρ d n e).E :=
  roughVectorSpatialLift (cubeSpatialVariableEquiv d)
    (nativeResidueCubeBoundedPolynomial D F ρ hρ d n e p hp)

noncomputable def nativeResidueCubeSpatialOrbit {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (x : Option (Fin (d+1)) → ℝ) : (nativeResidueCubeData D F ρ hρ d n e).G :=
  nativeLieExponential (E := (nativeResidueCubeData D F ρ hρ d n e).E)
    (I := (nativeResidueCubeData D F ρ hρ d n e).I) (G := (nativeResidueCubeData D F ρ hρ d n e).G)
    (roughVectorMvEval (E := (nativeResidueCubeData D F ρ hρ d n e).E)
      (nativeResidueCubeSourcePolynomial D F ρ hρ d n e p hp)
      (fun i => x (some (cubeSpatialVariableEquiv d i))))

theorem native_residue_cube_spatial_degree {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) :
    RoughVectorMvDegreeLE (nativeResidueCubeSpatialPolynomial D F ρ hρ d n e p hp) ℓ :=
  rough_vector_spatial_lift_degree _ _ ℓ (native_residue_cube_bounded_degree D F ρ hρ d n e p hp)

theorem native_residue_cube_spatial_log {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (x : Option (Fin (d+1)) → ℝ) :
    nativeLieGlobalLogarithm (E := (nativeResidueCubeData D F ρ hρ d n e).E)
      (I := (nativeResidueCubeData D F ρ hρ d n e).I) (G := (nativeResidueCubeData D F ρ hρ d n e).G)
      (nativeResidueCubeSpatialOrbit D F ρ hρ d n e p hp x) =
      roughVectorMvEval (nativeResidueCubeSpatialPolynomial D F ρ hρ d n e p hp) x := by
  rw [nativeResidueCubeSpatialPolynomial, rough_vector_spatial_lift_eval]
  exact native_residue_cube_bounded_original_log D F ρ hρ d n e p hp _

theorem native_residue_cube_spatial_projection {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (chi : (nativeResidueCubeData D F ρ hρ d n e).E →ₗ[ℝ] ℝ) (z : ℝ) :
    roughScalarSpatialProjection chi (nativeResidueCubeSpatialPolynomial D F ρ hρ d n e p hp) z =
      MvPolynomial.rename (cubeSpatialVariableEquiv d)
        (roughVectorMvProjection chi (nativeResidueCubeSourcePolynomial D F ρ hρ d n e p hp)) := by
  rw [nativeResidueCubeSpatialPolynomial, rough_vector_spatial_lift_projection,
    native_residue_cube_bounded_projection]

theorem native_residue_cube_spatial_top_coefficient {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (chi : (nativeResidueCubeData D F ρ hρ d n e).E →ₗ[ℝ] ℝ)
    (j : ℕ) (A : Finset (Fin d)) (hA : A.card ≤ j)
    (hdeg : (roughVectorMvProjection chi (nativeResidueCubeSourcePolynomial D F ρ hρ d n e p hp)).totalDegree ≤ j)
    (z : ℝ) (b : Fin (d+1) → ℝ) (t : ℝ) :
    MvPolynomial.coeff (cubeSpatialMonomial j A)
      (roughMvAffineSubstitution b (fun _ => t)
        (roughScalarSpatialProjection chi (nativeResidueCubeSpatialPolynomial D F ρ hρ d n e p hp) z)) =
      t^j * MvPolynomial.coeff (cubeIsolatedMonomial j A)
        (roughVectorMvProjection chi (nativeResidueCubeSourcePolynomial D F ρ hρ d n e p hp)) := by
  rw [native_residue_cube_spatial_projection]
  exact cube_spatial_top_coefficient j A hA _ hdeg b t

theorem native_residue_cube_spatial_original_vertices {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (z : ℝ) (x : Fin (d+1) → ℝ) (a : Fin (n+1)) :
    nativeFiniteProductCoordinate n (nativeRationalCubeGroupInclusion D F d n e
      (nativeResidueCubeSpatialOrbit D F ρ hρ d n e p hp (fun i => i.elim z x))) a =
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) p (fun _ => x 0 + ∑ i ∈ e a, x i.succ)) := by
  have he := native_residue_cube_source_original_vertices D F ρ hρ d n e p hp
    (fun i => x (cubeSpatialVariableEquiv d i)) a
  unfold nativeResidueCubeSpatialOrbit
  simpa only [Option.elim_some, cube_spatial_variable_none, cube_spatial_variable_some] using he

end Hindman168
