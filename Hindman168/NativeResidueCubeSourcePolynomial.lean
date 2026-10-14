import Hindman168.NativeCubeSourceProjection
import Hindman168.NativeResidueCubeScalarCoefficient

/-! The actual rational-residue cube source, retaining all original vertices
and filtration layers. Its genuine horizontal projection is the explicit sum. -/
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

theorem native_conjugate_taylor_residual_eval {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (ρ : D.G)
    (p : RoughVectorMvPolynomial Unit D.E) (k : ℕ) (x : Unit → ℝ) :
    roughVectorMvEval (E := D.E) (adaptedTaylorResidual (nativeConjugateNilmanifoldData D ρ) p k) x =
      roughVectorMvEval (E := D.E) (adaptedTaylorResidual D p k) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    have hL := adapted_taylor_removal_eval (nativeConjugateNilmanifoldData D ρ)
      (adaptedTaylorResidual (nativeConjugateNilmanifoldData D ρ) p k) k x
    have hR := adapted_taylor_removal_eval D (adaptedTaylorResidual D p k) k x
    apply hL.trans
    apply Eq.trans _ hR.symm
    change nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (-(MvPolynomial.eval x (adaptedTaylorBinomial k)) •
          roughVectorMvEval (E := D.E) (adaptedTaylorResidual (nativeConjugateNilmanifoldData D ρ) p k)
            (fun _ => (k : ℝ))) *
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) (adaptedTaylorResidual (nativeConjugateNilmanifoldData D ρ) p k) x)) = _
    rw [ih, ih]

noncomputable def nativeResidueCubeSourcePolynomial {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) :
    RoughVectorMvPolynomial (Option (Fin d)) (nativeResidueCubeData D F ρ hρ d n e).E :=
  nativeCubeSourcePolynomial (nativeConjugateNilmanifoldData D ρ)
    (nativeConjugateSubgroupFiltration D F ρ hρ) d n e p hp (ℓ+1)

theorem native_residue_cube_source_weighted {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) :
    RoughVectorMvWeightedDegree (nativeResidueCubeFiltration D F ρ hρ d n e).layer
      (nativeResidueCubeSourcePolynomial D F ρ hρ d n e p hp) 0 :=
  native_cube_source_polynomial_weighted (nativeConjugateNilmanifoldData D ρ)
    (nativeConjugateSubgroupFiltration D F ρ hρ) d n e p hp (ℓ+1)

theorem native_residue_cube_source_filtered {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) :
    RoughFilteredPolynomial (nativeRationalSubgroupLayer (nativeResidueCubeData D F ρ hρ d n e)
      (nativeRationalSubgroupFiltrationOfFull _ (nativeResidueCubeFiltration D F ρ hρ d n e)))
      (fun b : Option (Fin d) → ℝ => nativeLieExponential
        (E := (nativeResidueCubeData D F ρ hρ d n e).E)
        (I := (nativeResidueCubeData D F ρ hρ d n e).I)
        (G := (nativeResidueCubeData D F ρ hρ d n e).G)
        (roughVectorMvEval (E := (nativeResidueCubeData D F ρ hρ d n e).E)
          (nativeResidueCubeSourcePolynomial D F ρ hρ d n e p hp) b)) :=
  native_rational_subgroup_polynomial_filtered (nativeResidueCubeData D F ρ hρ d n e)
    (nativeRationalSubgroupFiltrationOfFull _ (nativeResidueCubeFiltration D F ρ hρ d n e)) _
    (native_residue_cube_source_weighted D F ρ hρ d n e p hp)

theorem native_residue_cube_source_original_vertices {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (b : Option (Fin d) → ℝ) (a : Fin (n+1)) :
    nativeFiniteProductCoordinate n (nativeRationalCubeGroupInclusion D F d n e
      (nativeLieExponential (E := (nativeResidueCubeData D F ρ hρ d n e).E)
        (I := (nativeResidueCubeData D F ρ hρ d n e).I) (G := (nativeResidueCubeData D F ρ hρ d n e).G)
        (roughVectorMvEval (E := (nativeResidueCubeData D F ρ hρ d n e).E)
          (nativeResidueCubeSourcePolynomial D F ρ hρ d n e p hp) b))) a =
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) p (fun _ => b none + ∑ i ∈ e a, b (some i))) :=
  native_cube_source_polynomial_original_vertices (nativeConjugateNilmanifoldData D ρ)
    (nativeConjugateSubgroupFiltration D F ρ hρ) d n e p hp b a

theorem native_residue_cube_source_projection {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (chi : (nativeResidueCubeData D F ρ hρ d n e).E →ₗ[ℝ] ℝ)
    (hChi : RoughNativeHorizontalFunctional (I := (nativeResidueCubeData D F ρ hρ d n e).I)
      (nativeResidueCubeData D F ρ hρ d n e).Γ chi) :
    roughVectorMvProjection chi (nativeResidueCubeSourcePolynomial D F ρ hρ d n e p hp) =
      nativeResidueCubeTaylorScalarPolynomial D F ρ hρ d n e chi p := by
  have he := native_cube_source_polynomial_projection (nativeConjugateNilmanifoldData D ρ)
    (nativeConjugateSubgroupFiltration D F ρ hρ) d n e p hp chi hChi (ℓ+1)
  apply he.trans
  unfold nativeResidueCubeTaylorScalarPolynomial cubeTaylorFaceScalarPolynomial
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro A _
  apply congrArg (fun c : ℝ => MvPolynomial.C c * cubeBinomialFacePolynomial k A)
  exact congrArg (nativeResidueCubeFaceFunctional D F ρ hρ d n e chi A)
    (native_conjugate_taylor_residual_eval D ρ p k (fun _ => (k : ℝ)))

end Hindman168
