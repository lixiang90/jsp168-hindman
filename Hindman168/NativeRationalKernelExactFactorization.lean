import Hindman168.NativeRationalFunctionalScalarPolynomial
import Hindman168.NativeRationalKernelCollectedPolynomial

/-! A GENUINE exact source factorization in the smaller kernel filtration.
The nonlinear scalar factor is explicit and may be UNBOUNDED. No small/
rational split or correlation transfer is claimed before it is proved. -/
namespace Hindman168
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalKernelExactResidual {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : D.E →L[ℝ] ℝ)
    (p : RoughVectorMvPolynomial Unit D.E) (y : D.E) : RoughVectorMvPolynomial Unit D.E :=
  nativeRationalKernelCollectedPolynomial D (roughNativeProductMvPolynomial (I := D.I) (G := D.G)
    [(unitMvNonlinearPart (roughVectorMvProjection F.toLinearMap p),-y)] p)

theorem native_rational_kernel_exact_residual_projection {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : D.E →L[ℝ] ℝ)
    (hF : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ F.toLinearMap.ker)
    (p : RoughVectorMvPolynomial Unit D.E) (y : D.E) (hy : F y=1) :
    let P := roughVectorMvProjection F.toLinearMap p
    roughVectorMvProjection F.toLinearMap (nativeRationalKernelExactResidual D F p y) =
      MvPolynomial.C (P.coeff 0)+MvPolynomial.C (P.coeff (Finsupp.single () 1))*MvPolynomial.X () := by
  rw [nativeRationalKernelExactResidual,native_rational_kernel_collected_polynomial_projection,
    native_rational_product_horizontal_projection D F hF]
  change unitMvNonlinearPart (roughVectorMvProjection F.toLinearMap p)*MvPolynomial.C (F (-y))+0+
    roughVectorMvProjection F.toLinearMap p = _
  rw [map_neg,hy]
  simp only [MvPolynomial.C_neg,map_one,mul_neg,mul_one,add_zero]
  dsimp only [unitMvNonlinearPart]
  ring

theorem native_rational_kernel_exact_residual_weighted_degree {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (F : D.E →L[ℝ] ℝ)
    (hF : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ F.toLinearMap.ker)
    (hRat : ∀ v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ, ∃ q : ℚ, F v = (q : ℝ))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (j : ℕ) (hj : 1 ≤ j) (y : D.E) (hy : y ∈ L.layer j) (hFy : F y=1)
    (hHigher : L.layer (j+1) ≤ F.toLinearMap.ker) :
    RoughVectorMvWeightedDegree (nativeRationalKernelLieFiltration D L F hF hRat).layer
      (nativeRationalKernelExactResidual D F p y) 0 ∧
    RoughVectorMvDegreeLE (nativeRationalKernelExactResidual D F p y) ℓ := by
  let Q := unitMvNonlinearPart (roughVectorMvProjection F.toLinearMap p)
  have hQ : Q.totalDegree ≤ j := unit_mv_nonlinear_part_degree _ j hj
    (native_rational_functional_scalar_degree D L p hp F j hHigher)
  have hDirection : RoughVectorMvWeightedDegree L.layer ([(Q,-y)] : RoughVectorMvPolynomial Unit D.E) 0 := by
    rintro a ha
    have he : a=(Q,-y) := List.mem_singleton.mp ha
    subst a
    change -y ∈ L.layer (Q.totalDegree+0)
    rw [Nat.add_zero]
    exact L.antitone hQ ((L.layer j).neg_mem hy)
  have hRaw := native_rational_product_polynomial_weighted D L hDirection hp
  have hAffine : (roughVectorMvProjection F.toLinearMap
      (roughNativeProductMvPolynomial (I := D.I) (G := D.G) [(Q,-y)] p)).totalDegree ≤ 1 := by
    have he := native_rational_kernel_exact_residual_projection D F hF p y hFy
    rw [nativeRationalKernelExactResidual,native_rational_kernel_collected_polynomial_projection] at he
    rw [he]
    exact unit_mv_linear_part_degree _
  exact native_rational_kernel_collected_polynomial_weighted_degree D L F hF hRat _ hRaw hAffine

theorem native_rational_kernel_exact_residual_eval {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : D.E →L[ℝ] ℝ)
    (p : RoughVectorMvPolynomial Unit D.E) (y : D.E) (x : Unit → ℝ) :
    roughVectorMvEval (E := D.E) (nativeRationalKernelExactResidual D F p y) x =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (-(MvPolynomial.eval x (unitMvNonlinearPart (roughVectorMvProjection F.toLinearMap p)) • y)) *
            nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p x)) := by
  rw [nativeRationalKernelExactResidual,native_rational_kernel_collected_polynomial_eval,
    roughNativeProductMvPolynomial_eval]
  congr 2
  simp only [roughVectorMvEval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,smul_neg]

theorem native_rational_kernel_exact_factorization {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : D.E →L[ℝ] ℝ)
    (p : RoughVectorMvPolynomial Unit D.E) (y : D.E) (x : Unit → ℝ) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p x) =
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (MvPolynomial.eval x (unitMvNonlinearPart (roughVectorMvProjection F.toLinearMap p)) • y) *
          nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            (roughVectorMvEval (E := D.E) (nativeRationalKernelExactResidual D F p y) x) := by
  let a := MvPolynomial.eval x (unitMvNonlinearPart (roughVectorMvProjection F.toLinearMap p)) • y
  let g := nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p x)
  have hneg : nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (-a) =
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) a)⁻¹ :=
    nativeLieExponential_neg (E := D.E) (I := D.I) (G := D.G) a
  have hResidual : nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) (nativeRationalKernelExactResidual D F p y) x) =
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) a)⁻¹*g := by
    calc
      _ = nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
            (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (-a)*g)) :=
        congrArg (fun v : D.E => nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v)
          (native_rational_kernel_exact_residual_eval D F p y x)
      _ = nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (-a)*g :=
        nativeLieExponential_globalLogarithm (E := D.E) (I := D.I) (G := D.G) _
      _ = _ := congrArg (fun t : D.G => t*g) hneg
  change g = nativeLieExponential (E := D.E) (I := D.I) (G := D.G) a*_
  calc
    _ = nativeLieExponential (E := D.E) (I := D.I) (G := D.G) a*
        ((nativeLieExponential (E := D.E) (I := D.I) (G := D.G) a)⁻¹*g) := by group
    _ = _ := congrArg (fun t : D.G => nativeLieExponential (E := D.E) (I := D.I) (G := D.G) a*t) hResidual.symm

end Hindman168
