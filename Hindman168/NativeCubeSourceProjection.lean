import Hindman168.NativeCubeSourcePolynomial
import Hindman168.CubeTaylorNoCancellation

/-! Horizontal projection of the ACTUAL ordered cube polynomial is exactly
the scalar face/Taylor sum previously used to isolate a coefficient. -/
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

theorem native_subgroup_horizontal_polynomial_product {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (phi : D.E →ₗ[ℝ] ℝ)
    (hB : ∀ v ∈ F.layer 0, ∀ w ∈ F.layer 0,
      phi (nativeLieAdjointDifferential (I := D.I) (G := D.G) v w) = 0)
    (p q : RoughVectorMvPolynomial σ D.E)
    (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (hq : RoughVectorMvWeightedDegree F.layer q 0) :
    roughVectorMvProjection phi (roughNativeProductMvPolynomial (E := D.E) (I := D.I) (G := D.G) p q) =
      roughVectorMvProjection phi p + roughVectorMvProjection phi q := by
  apply MvPolynomial.funext
  intro b
  rw [MvPolynomial.eval_add, roughVectorMvProjection_eval, roughVectorMvProjection_eval,
    roughVectorMvProjection_eval]
  exact (congrArg phi (roughNativeProductMvPolynomial_eval (I := D.I) (G := D.G) p q b)).trans
    (native_subgroup_horizontal_product D F phi hB
      (rough_vector_weighted_eval F.layer F.antitone hp b)
      (rough_vector_weighted_eval F.layer F.antitone hq b))

theorem native_cube_source_polynomial_projection {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (chi : (nativeRationalCubeData D F d n e).E →ₗ[ℝ] ℝ)
    (hChi : RoughNativeHorizontalFunctional (I := (nativeRationalCubeData D F d n e).I)
      (nativeRationalCubeData D F d n e).Γ chi) (N : ℕ) :
    roughVectorMvProjection chi (nativeCubeSourcePolynomial D F d n e p hp N) =
      cubeTaylorFaceScalarPolynomial N (fun k A => nativeCubeFaceFunctional D F d n e chi A
        (roughVectorMvEval (adaptedTaylorResidual D p k) (fun _ => (k : ℝ)))) := by
  let C := nativeRationalCubeData D F d n e
  let K := nativeRationalSubgroupFiltrationOfFull C (nativeCubeRationalLieFiltration D F d n e)
  have hb : ∀ v ∈ K.layer 0, ∀ w ∈ K.layer 0,
      chi (nativeLieAdjointDifferential (I := C.I) (G := C.G) v w) = 0 := by
    intro v _ w _
    exact hChi.2.1 (native_rational_lie_bracket_mem_commutator C v w)
  induction N with
  | zero => simp only [nativeCubeSourcePolynomial, roughVectorMvProjection,
      cubeTaylorFaceScalarPolynomial, Finset.range_zero, Finset.sum_empty]
  | succ k ih =>
    have hq : RoughVectorMvWeightedDegree K.layer
        (nativeCubeSourceTaylorFactorPolynomial D F d n e p hp k) 0 :=
      native_cube_taylor_factor_weighted D F d n e k _ _
    rw [nativeCubeSourcePolynomial,
      native_subgroup_horizontal_polynomial_product C K chi hb
        (nativeCubeSourcePolynomial D F d n e p hp k)
        (nativeCubeSourceTaylorFactorPolynomial D F d n e p hp k)
        (native_cube_source_polynomial_weighted D F d n e p hp k) hq, ih]
    simp only [cubeTaylorFaceScalarPolynomial, Finset.sum_range_succ]
    congr 1
    exact native_cube_taylor_factor_projection D F d n e k _ _ chi

end Hindman168
