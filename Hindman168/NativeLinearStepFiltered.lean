import Hindman168.NativeLinearStepPolynomial
import Hindman168.NativeArbitraryLieFilteredPolynomial
import Hindman168.NativeBasepointTrimmedPolynomial

/-! Linear-step lattice correction keeps the SAME original stretched
filtration, even after basepoint normalization raises ordinary degree. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_linear_step_real_polynomial_filtered {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    {p : RoughVectorMvPolynomial Unit D.E}
    (hp : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d) p 0)
    (γ : D.G) :
    RoughFilteredPolynomial (roughStretchedLowerCentralFiltration D.G d)
      (fun x : Unit → ℝ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) (nativeLinearStepPolynomial D p γ) x)) :=
  native_arbitrary_lie_polynomial_filtered D
    (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d)
    (rough_native_stretched_lie_antitone d hd)
    (fun _ _ _ _ hv hw => rough_native_stretched_lie_bracket d hd hv hw)
    (roughStretchedLowerCentralFiltration D.G d)
    (fun i v hv => (rough_native_stretched_filtration_exp_mem_iff (I := D.I) d i v).mpr hv) _
    (native_linear_step_polynomial_weighted D d hd hp γ)

theorem native_linear_step_integer_polynomial_filtered {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    {p : RoughVectorMvPolynomial Unit D.E}
    (hp : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d) p 0)
    (γ : D.G) :
    RoughFilteredPolynomial (roughStretchedLowerCentralFiltration D.G d)
      (fun n : ℤ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) (nativeLinearStepPolynomial D p γ) (fun _ => (n : ℝ)))) := by
  let c : ℤ →+ (Unit → ℝ) := {
    toFun := fun n _ => (n : ℝ)
    map_zero' := by funext j; exact Int.cast_zero
    map_add' := by intro n m; funext j; exact Int.cast_add _ _ }
  exact rough_filtered_polynomial_precompose _ _
    (native_linear_step_real_polynomial_filtered D d hd hp γ) c

theorem native_basepoint_linear_step_polynomial_weighted {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d) (r γ : D.G) :
    RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d)
      (nativeLinearStepPolynomial D (nativeBasepointPolynomial D p r) γ) 0 :=
  native_linear_step_polynomial_weighted D d hd (native_basepoint_polynomial_weighted D d hd p hp r) γ

end Hindman168
