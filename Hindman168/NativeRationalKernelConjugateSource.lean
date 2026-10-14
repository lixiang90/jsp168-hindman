import Hindman168.NativeRationalKernelCollectedPolynomial
import Hindman168.NativeRationalFunctionalScalarPolynomial

/-! ACTUAL variable conjugation by an old-weighted direction polynomial
constructs a TRUE kernel-filtered source after genuine aggregate collection.
The conjugating polynomial itself need not be kernel-filtered. -/
namespace Hindman168
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalKernelConjugateSource {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (R : MvPolynomial σ ℝ) (y : D.E)
    (p : RoughVectorMvPolynomial σ D.E) : RoughVectorMvPolynomial σ D.E :=
  nativeRationalKernelCollectedPolynomial D
    (roughNativeProductMvPolynomial (I := D.I) (G := D.G)
      (roughNativeProductMvPolynomial (I := D.I) (G := D.G) [(R,y)] p) [(R,-y)])

theorem native_rational_kernel_conjugate_source_projection {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : D.E →L[ℝ] ℝ)
    (hF : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ F.toLinearMap.ker)
    (R : MvPolynomial σ ℝ) (y : D.E) (p : RoughVectorMvPolynomial σ D.E) :
    roughVectorMvProjection F.toLinearMap (nativeRationalKernelConjugateSource D R y p)=
      roughVectorMvProjection F.toLinearMap p := by
  rw [nativeRationalKernelConjugateSource,native_rational_kernel_collected_polynomial_projection,
    native_rational_product_horizontal_projection D F hF,
    native_rational_product_horizontal_projection D F hF]
  change (R*MvPolynomial.C (F y)+0+roughVectorMvProjection F.toLinearMap p)+
    (R*MvPolynomial.C (F (-y))+0)=_
  rw [map_neg,MvPolynomial.C_neg]
  ring

theorem native_rational_kernel_conjugate_source_weighted_degree {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (F : D.E →L[ℝ] ℝ)
    (hF : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ F.toLinearMap.ker)
    (hRat : ∀ v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ, ∃ q : ℚ, F v=(q : ℝ))
    (R : MvPolynomial σ ℝ) (j : ℕ) (hR : R.totalDegree ≤ j)
    (y : D.E) (hy : y ∈ L.layer j) (p : RoughVectorMvPolynomial σ D.E)
    (hp : RoughVectorMvWeightedDegree (nativeRationalKernelLieFiltration D L F hF hRat).layer p 0) :
    RoughVectorMvWeightedDegree (nativeRationalKernelLieFiltration D L F hF hRat).layer
      (nativeRationalKernelConjugateSource D R y p) 0 ∧
    RoughVectorMvDegreeLE (nativeRationalKernelConjugateSource D R y p) ℓ := by
  have hOld : RoughVectorMvWeightedDegree L.layer p 0 := by
    intro a ha
    exact native_rational_kernel_lie_filtration_layer_le D L F hF hRat _ (hp a ha)
  have hDirection (v : D.E) (hv : v ∈ L.layer j) :
      RoughVectorMvWeightedDegree L.layer ([(R,v)] : RoughVectorMvPolynomial σ D.E) 0 := by
    rintro a ha
    have he : a=(R,v) := List.mem_singleton.mp ha
    subst a
    change v ∈ L.layer (R.totalDegree+0)
    rw [Nat.add_zero]
    exact L.antitone hR hv
  have hRaw := native_rational_product_polynomial_weighted D L
    (native_rational_product_polynomial_weighted D L (hDirection y hy) hOld)
    (hDirection (-y) ((L.layer j).neg_mem hy))
  have hAffine : (roughVectorMvProjection F.toLinearMap p).totalDegree ≤ 1 :=
    native_rational_functional_scalar_degree D (nativeRationalKernelLieFiltration D L F hF hRat)
      p hp F 1 (by
        rw [native_rational_kernel_lie_filtration_layer,if_pos (by omega : 2 ≤ 1+1)]
        exact inf_le_right)
  have hProjection := native_rational_kernel_conjugate_source_projection D F hF R y p
  rw [nativeRationalKernelConjugateSource,native_rational_kernel_collected_polynomial_projection] at hProjection
  exact native_rational_kernel_collected_polynomial_weighted_degree D L F hF hRat _ hRaw
    (by rw [hProjection]; exact hAffine)

theorem native_rational_kernel_conjugate_source_exponential {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (R : MvPolynomial σ ℝ) (y : D.E)
    (p : RoughVectorMvPolynomial σ D.E) (x : σ → ℝ) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) (nativeRationalKernelConjugateSource D R y p) x)=
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (MvPolynomial.eval x R • y)*
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p x)*
          (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (MvPolynomial.eval x R • y))⁻¹ := by
  rw [nativeRationalKernelConjugateSource,native_rational_kernel_collected_polynomial_eval,
    roughNativeProductMvPolynomial_eval,nativeLieExponential_globalLogarithm,
    roughNativeProductMvPolynomial_eval,nativeLieExponential_globalLogarithm]
  have hEval : roughVectorMvEval (E := D.E) ([(R,y)] : RoughVectorMvPolynomial σ D.E) x=
      MvPolynomial.eval x R • y := by
    simp only [roughVectorMvEval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  have hInv : roughVectorMvEval (E := D.E) ([(R,-y)] : RoughVectorMvPolynomial σ D.E) x=
      -(MvPolynomial.eval x R • y) := by
    simp only [roughVectorMvEval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,smul_neg]
  rw [hEval,hInv]
  exact congrArg (fun g : D.G =>
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (MvPolynomial.eval x R • y)*
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p x)*g)
    (nativeLieExponential_neg (E := D.E) (I := D.I) (G := D.G) (MvPolynomial.eval x R • y))

end Hindman168
