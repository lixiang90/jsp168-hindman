import Hindman168.NativeResidueCubeActualCoefficient
import Hindman168.RoughVectorZeroTrimProjection

/-! A degree-bounded representation of the ACTUAL cube source, removing only
zero vector terms and retaining all values and projected coefficients. -/
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

noncomputable def nativeResidueCubeBoundedPolynomial {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) :
    RoughVectorMvPolynomial (Option (Fin d)) (nativeResidueCubeData D F ρ hρ d n e).E :=
  roughVectorMvZeroTrim (nativeResidueCubeSourcePolynomial D F ρ hρ d n e p hp)

theorem native_residue_cube_bounded_degree {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) :
    RoughVectorMvDegreeLE (nativeResidueCubeBoundedPolynomial D F ρ hρ d n e p hp) ℓ := by
  exact rough_vector_zero_trim_degree (nativeResidueCubeFiltration D F ρ hρ d n e).layer
    (nativeResidueCubeFiltration D F ρ hρ d n e).antitone
    (native_residue_cube_source_weighted D F ρ hρ d n e p hp)
    (nativeResidueCubeFiltration D F ρ hρ d n e).terminal

theorem native_residue_cube_bounded_eval {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (b : Option (Fin d) → ℝ) :
    roughVectorMvEval (nativeResidueCubeBoundedPolynomial D F ρ hρ d n e p hp) b =
      roughVectorMvEval (nativeResidueCubeSourcePolynomial D F ρ hρ d n e p hp) b :=
  rough_vector_zero_trim_eval _ _

theorem native_residue_cube_bounded_projection {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (chi : (nativeResidueCubeData D F ρ hρ d n e).E →ₗ[ℝ] ℝ) :
    roughVectorMvProjection chi (nativeResidueCubeBoundedPolynomial D F ρ hρ d n e p hp) =
      roughVectorMvProjection chi (nativeResidueCubeSourcePolynomial D F ρ hρ d n e p hp) :=
  rough_vector_zero_trim_projection chi _

theorem native_residue_cube_bounded_original_log {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (b : Option (Fin d) → ℝ) :
    nativeLieGlobalLogarithm (E := (nativeResidueCubeData D F ρ hρ d n e).E)
      (I := (nativeResidueCubeData D F ρ hρ d n e).I) (G := (nativeResidueCubeData D F ρ hρ d n e).G)
      (nativeLieExponential (E := (nativeResidueCubeData D F ρ hρ d n e).E)
        (I := (nativeResidueCubeData D F ρ hρ d n e).I) (G := (nativeResidueCubeData D F ρ hρ d n e).G)
        (roughVectorMvEval (E := (nativeResidueCubeData D F ρ hρ d n e).E)
          (nativeResidueCubeSourcePolynomial D F ρ hρ d n e p hp) b)) =
      roughVectorMvEval (nativeResidueCubeBoundedPolynomial D F ρ hρ d n e p hp) b := by
  rw [nativeLieGlobalLogarithm_exponential, native_residue_cube_bounded_eval]

end Hindman168
