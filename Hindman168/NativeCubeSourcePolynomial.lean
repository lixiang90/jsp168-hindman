import Hindman168.NativeCubeTaylorFactorPolynomial

/-! The actual ordered cube polynomial from the SAME original source. -/
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

noncomputable def nativeCubeSourceTaylorFactorPolynomial {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (k : ℕ) : RoughVectorMvPolynomial (Option (Fin d)) (nativeRationalCubeData D F d n e).E :=
  nativeCubeTaylorFactorPolynomial D F d n e k
    (roughVectorMvEval (adaptedTaylorResidual D p k) (fun _ => (k : ℝ)))
    (native_rational_subgroup_taylor_initial_value_layer D F _
      (native_rational_subgroup_taylor_residual_properties D F p hp k).1 k
      (native_rational_subgroup_taylor_residual_properties D F p hp k).2)

noncomputable def nativeCubeSourcePolynomial {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) :
    ℕ → RoughVectorMvPolynomial (Option (Fin d)) (nativeRationalCubeData D F d n e).E
  | 0 => []
  | k+1 => roughNativeProductMvPolynomial (E := (nativeRationalCubeData D F d n e).E)
      (I := (nativeRationalCubeData D F d n e).I) (G := (nativeRationalCubeData D F d n e).G)
      (nativeCubeSourcePolynomial D F d n e p hp k)
      (nativeCubeSourceTaylorFactorPolynomial D F d n e p hp k)

theorem native_cube_source_polynomial_weighted {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (N : ℕ) :
    RoughVectorMvWeightedDegree (nativeCubeInternalLayer D F d n e)
      (nativeCubeSourcePolynomial D F d n e p hp N) 0 := by
  induction N with
  | zero => intro a ha; exact False.elim (List.not_mem_nil ha)
  | succ k ih =>
    exact native_rational_subgroup_product_weighted (nativeRationalCubeData D F d n e)
      (nativeRationalSubgroupFiltrationOfFull _ (nativeCubeRationalLieFiltration D F d n e))
      ih (native_cube_taylor_factor_weighted D F d n e k _ _)

theorem native_cube_source_taylor_factor_coordinate {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (k : ℕ) (b : Option (Fin d) → ℝ) (a : Fin (n+1)) :
    nativeFiniteProductCoordinate n (nativeRationalCubeGroupInclusion D F d n e
      (nativeLieExponential (E := (nativeRationalCubeData D F d n e).E)
        (I := (nativeRationalCubeData D F d n e).I) (G := (nativeRationalCubeData D F d n e).G)
        (roughVectorMvEval (E := (nativeRationalCubeData D F d n e).E)
          (nativeCubeSourceTaylorFactorPolynomial D F d n e p hp k) b))) a =
      adaptedTaylorFactor D (adaptedTaylorResidual D p k) k
        (b none + ∑ i ∈ e a, b (some i)) := by
  rw [nativeCubeSourceTaylorFactorPolynomial, native_cube_taylor_factor_exponential_coordinate]
  rw [adaptedTaylorFactor, ← adapted_taylor_binomial_scalar, scalar_unit_polynomial_eval]

theorem native_cube_source_polynomial_coordinate {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (N : ℕ) (b : Option (Fin d) → ℝ) (a : Fin (n+1)) :
    nativeFiniteProductCoordinate n (nativeRationalCubeGroupInclusion D F d n e
      (nativeLieExponential (E := (nativeRationalCubeData D F d n e).E)
        (I := (nativeRationalCubeData D F d n e).I) (G := (nativeRationalCubeData D F d n e).G)
        (roughVectorMvEval (E := (nativeRationalCubeData D F d n e).E)
          (nativeCubeSourcePolynomial D F d n e p hp N) b))) a =
      adaptedTaylorOrderedProduct D p (b none + ∑ i ∈ e a, b (some i)) N := by
  induction N with
  | zero =>
    change nativeFiniteProductCoordinate n (nativeRationalCubeGroupInclusion D F d n e
      (nativeLieExponential (E := (nativeRationalCubeData D F d n e).E)
        (I := (nativeRationalCubeData D F d n e).I) (G := (nativeRationalCubeData D F d n e).G) 0)) a = 1
    rw [nativeLieExponential_zero, map_one, native_finite_product_coordinate_one]
  | succ k ih =>
    rw [nativeCubeSourcePolynomial, roughNativeProductMvPolynomial_eval,
      nativeLieExponential_globalLogarithm, map_mul, native_finite_product_coordinate_mul,
      ih, native_cube_source_taylor_factor_coordinate, adaptedTaylorOrderedProduct]

theorem native_cube_source_polynomial_original_vertices {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (b : Option (Fin d) → ℝ) (a : Fin (n+1)) :
    nativeFiniteProductCoordinate n (nativeRationalCubeGroupInclusion D F d n e
      (nativeLieExponential (E := (nativeRationalCubeData D F d n e).E)
        (I := (nativeRationalCubeData D F d n e).I) (G := (nativeRationalCubeData D F d n e).G)
        (roughVectorMvEval (E := (nativeRationalCubeData D F d n e).E)
          (nativeCubeSourcePolynomial D F d n e p hp (ℓ+1)) b))) a =
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) p (fun _ => b none + ∑ i ∈ e a, b (some i))) := by
  rw [native_cube_source_polynomial_coordinate]
  exact (native_rational_subgroup_taylor_ordered_representation D F p hp _).symm

end Hindman168
