import Hindman168.NativeCubeTaylorFaceVector
import Hindman168.CubeBooleanExpansion

/-! Actual single Taylor factors in the internal cube model, with weighted
adaptation, exact original vertex exponentials and horizontal projection. -/
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

noncomputable def nativeCubeTaylorFactorPolynomial {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (k : ℕ)
    (v : D.E) (hv : v ∈ F.layer k) :
    RoughVectorMvPolynomial (Option (Fin d)) (nativeRationalCubeData D F d n e).E :=
  (Finset.univ : Finset (Finset (Fin d))).toList.map (fun A =>
    (cubeBinomialFacePolynomial k A, nativeCubeTaylorFaceVector D F d n e k A v hv))

theorem native_cube_taylor_factor_weighted {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (k : ℕ)
    (v : D.E) (hv : v ∈ F.layer k) :
    RoughVectorMvWeightedDegree (nativeCubeInternalLayer D F d n e)
      (nativeCubeTaylorFactorPolynomial D F d n e k v hv) 0 := by
  intro z hz
  obtain ⟨A,_,rfl⟩ := List.mem_map.mp hz
  exact native_cube_internal_antitone D F d n e
    (by simpa only [Nat.add_zero] using cube_binomial_face_degree k A)
    (native_cube_taylor_face_vector_layer D F d n e k A v hv)

theorem native_cube_taylor_factor_eval {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (k : ℕ)
    (v : D.E) (hv : v ∈ F.layer k) (b : Option (Fin d) → ℝ) :
    roughVectorMvEval (nativeCubeTaylorFactorPolynomial D F d n e k v hv) b =
      ∑ A : Finset (Fin d), MvPolynomial.eval b (cubeBinomialFacePolynomial k A) •
        nativeCubeTaylorFaceVector D F d n e k A v hv := by
  simp only [nativeCubeTaylorFactorPolynomial, roughVectorMvEval, List.map_map,
    Function.comp_def, Finset.sum_map_toList]

theorem native_cube_taylor_factor_coordinate {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (k : ℕ)
    (v : D.E) (hv : v ∈ F.layer k) (b : Option (Fin d) → ℝ) (a : Fin (n+1)) :
    nativeFiniteProductCoordinate n (nativeRationalCubeModelInclusion D F d n e
      (roughVectorMvEval (nativeCubeTaylorFactorPolynomial D F d n e k v hv) b)) a =
      (scalarBinomialPolynomial k).eval (b none + ∑ i ∈ e a, b (some i)) • v := by
  classical
  rw [← native_finite_product_coordinate_linear_apply]
  simp only [native_cube_taylor_factor_eval, map_sum, map_smul,
    native_finite_product_coordinate_linear_apply, native_cube_taylor_face_vector_coordinate]
  rw [cube_boolean_binomial_expansion, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro A _
  by_cases hA : A.card ≤ k
  · rw [if_pos hA]
    by_cases hV : A ⊆ e a <;> simp [hV]
  · rw [if_neg hA, cube_binomial_face_eq_zero k A (by omega)]
    simp

theorem native_cube_taylor_factor_projection {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (k : ℕ)
    (v : D.E) (hv : v ∈ F.layer k)
    (chi : (nativeRationalCubeData D F d n e).E →ₗ[ℝ] ℝ) :
    roughVectorMvProjection chi (nativeCubeTaylorFactorPolynomial D F d n e k v hv) =
      ∑ A : Finset (Fin d), MvPolynomial.C (nativeCubeFaceFunctional D F d n e chi A v) *
        cubeBinomialFacePolynomial k A := by
  classical
  apply MvPolynomial.funext
  intro b
  simp only [roughVectorMvProjection_eval, native_cube_taylor_factor_eval,
    map_sum, map_smul, smul_eq_mul, native_cube_taylor_face_vector_functional,
    map_mul, MvPolynomial.eval_C]
  apply Finset.sum_congr rfl
  intro A _
  by_cases hA : A.card ≤ k
  · rw [if_pos hA, mul_comm]
  · rw [if_neg hA, cube_binomial_face_eq_zero k A (by omega)]
    simp

theorem native_cube_taylor_factor_exponential_coordinate {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (k : ℕ)
    (v : D.E) (hv : v ∈ F.layer k) (b : Option (Fin d) → ℝ) (a : Fin (n+1)) :
    nativeFiniteProductCoordinate n (nativeRationalCubeGroupInclusion D F d n e
      (nativeLieExponential (E := (nativeRationalCubeData D F d n e).E) (I := (nativeRationalCubeData D F d n e).I)
        (G := (nativeRationalCubeData D F d n e).G)
        (roughVectorMvEval (E := (nativeRationalCubeData D F d n e).E)
          (nativeCubeTaylorFactorPolynomial D F d n e k v hv) b))) a =
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        ((scalarBinomialPolynomial k).eval (b none + ∑ i ∈ e a, b (some i)) • v) := by
  let z := roughVectorMvEval (nativeCubeTaylorFactorPolynomial D F d n e k v hv) b
  have h1 := congrArg (fun g => nativeFiniteProductCoordinate n g a)
    (native_rational_cube_data_exponential D F d n e z)
  have h2 := nativeFiniteProductExponential_coordinate (I := D.I) (G := D.G) n
    (nativeRationalCubeModelInclusion D F d n e z) a
  exact h1.trans (h2.trans (congrArg (nativeLieExponential (E := D.E) (I := D.I) (G := D.G))
    (native_cube_taylor_factor_coordinate D F d n e k v hv b a)))

end Hindman168
