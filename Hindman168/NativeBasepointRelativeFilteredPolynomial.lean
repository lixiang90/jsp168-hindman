import Hindman168.NativeBasepointRelativePolynomialWeights
import Hindman168.NativeRelativeLieExponentialLayers
import Hindman168.NativeArbitraryLieFilteredPolynomial

/-! ACTUAL original normalized relative coefficient polynomial is genuinely
filtered for SAME actual original internal relative filtration. All native
Lie bracket/exponential/weight inputs are discharged from original data. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_basepoint_relative_real_polynomial_filtered {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) :
    RoughFilteredPolynomial (nativeRelativeSquareInternalFiltration D d)
      (fun x : Unit → ℝ => nativeLieExponential (E := (nativeRelativeSquareData D d hd 1).E)
        (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G)
        (roughVectorMvEval (E := (nativeRelativeSquareData D d hd 1).E)
          (nativeBasepointRelativePolynomial D d hd p hp r t h) x)) :=
  native_arbitrary_lie_polynomial_filtered (nativeRelativeSquareData D d hd 1)
    (nativeRelativeLieFiltration D d hd) (native_relative_lie_filtration_antitone D d hd)
    (fun _ _ _ _ hv hw => native_relative_lie_filtration_bracket D d hd hv hw)
    (nativeRelativeSquareInternalFiltration D d)
    (fun i _ hv => native_relative_lie_filtration_exponential_mem D d hd i hv) _
    (native_basepoint_relative_polynomial_weighted D d hd p hp r t h)

theorem native_basepoint_relative_integer_polynomial_filtered {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) :
    RoughFilteredPolynomial (nativeRelativeSquareInternalFiltration D d)
      (nativeBasepointRelativeIntegerPair D d hd p hp r t h) := by
  let c : ℤ →+ (Unit → ℝ) := {
    toFun := fun n _ => (n : ℝ)
    map_zero' := by funext j; exact Int.cast_zero
    map_add' := by intro n m; funext j; exact Int.cast_add _ _ }
  have he := rough_filtered_polynomial_precompose _ _
    (native_basepoint_relative_real_polynomial_filtered D d hd p hp r t h) c
  have hFn : (fun n : ℤ => nativeLieExponential (E := (nativeRelativeSquareData D d hd 1).E)
      (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G)
      (roughVectorMvEval (E := (nativeRelativeSquareData D d hd 1).E)
        (nativeBasepointRelativePolynomial D d hd p hp r t h) (c n))) =
      nativeBasepointRelativeIntegerPair D d hd p hp r t h := by
    funext n
    exact native_basepoint_relative_polynomial_exponential D d hd p hp r t h n
  rw [hFn] at he
  exact he

end Hindman168
