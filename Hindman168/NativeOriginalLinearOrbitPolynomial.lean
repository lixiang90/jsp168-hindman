import Hindman168.NativeLinearStepPolynomial
import Hindman168.NativeLinearStepFiltered
import Hindman168.RoughVectorMvConstant

/-! A genuine linear native orbit has logarithmic weights in the ORIGINAL
lower central filtration. The parameter is exactly one; its terminal index
is the original step s, even when the product logarithm has higher degree
than the scalar input. No degree-dependent stretching is used. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_original_linear_orbit_constant_weighted {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (a : D.G) :
    RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) 1)
      (roughVectorMvConstant (σ := Unit)
        (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) a)) 0 := by
  apply rough_vector_constant_weighted
  rw [rough_native_stretched_lie_initial 1 (by omega) 0 (by omega)]
  exact Submodule.mem_top

noncomputable def nativeOriginalLeftLinearLog {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (g a : D.G) : RoughVectorMvPolynomial Unit D.E :=
  roughVectorMvZeroTrim (roughNativeProductMvPolynomial (I := D.I) (G := D.G)
    [(MvPolynomial.X (), nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g)]
    (roughVectorMvConstant (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) a)))

theorem native_original_left_linear_raw_weighted {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (g a : D.G) :
    RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) 1)
      (roughNativeProductMvPolynomial (I := D.I) (G := D.G)
        [(MvPolynomial.X (), nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g)]
        (roughVectorMvConstant (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) a))) 0 := by
  apply rough_native_product_polynomial_weighted 1 (by omega)
  · intro z hz
    obtain rfl := List.mem_singleton.mp hz
    rw [MvPolynomial.totalDegree_X, Nat.add_zero,
      rough_native_stretched_lie_initial 1 (by omega) 1 (by omega)]
    exact Submodule.mem_top
  · exact native_original_linear_orbit_constant_weighted D a

theorem native_original_left_linear_log_weighted {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (g a : D.G) :
    RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) 1)
      (nativeOriginalLeftLinearLog D g a) 0 :=
  rough_vector_zero_trim_weighted _ (native_original_left_linear_raw_weighted D g a)

theorem native_original_left_linear_log_degree {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (g a : D.G) :
    RoughVectorMvDegreeLE (nativeOriginalLeftLinearLog D g a) s := by
  simpa only [nativeOriginalLeftLinearLog, Nat.mul_one, Nat.sub_zero] using
    rough_vector_zero_trim_degree _ (rough_native_stretched_lie_antitone 1 (by omega))
      (native_original_left_linear_raw_weighted D g a)
      (rough_native_stretched_lie_terminal 1 (by omega) D.step_le)

theorem native_original_left_linear_log_eval {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (g a : D.G) (x : Unit → ℝ) :
    roughVectorMvEval (E := D.E) (nativeOriginalLeftLinearLog D g a) x =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (x () • nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) * a) := by
  rw [nativeOriginalLeftLinearLog, rough_vector_zero_trim_eval,
    roughNativeProductMvPolynomial_eval, rough_vector_constant_eval,
    nativeLieExponential_globalLogarithm]
  simp only [roughVectorMvEval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, MvPolynomial.eval_X]

theorem native_original_left_linear_integer_source {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (g a : D.G) (b : ℤ) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) (nativeOriginalLeftLinearLog D g a) (fun _ => (b : ℝ))) =
      g ^ b * a := by
  rw [native_original_left_linear_log_eval, nativeLieExponential_globalLogarithm,
    nativeLieExponential_int_smul, nativeLieExponential_globalLogarithm]

theorem native_original_left_linear_real_filtered {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (g a : D.G) :
    RoughFilteredPolynomial (roughStretchedLowerCentralFiltration D.G 1)
      (fun x : Unit → ℝ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) (nativeOriginalLeftLinearLog D g a) x)) :=
  native_arbitrary_lie_polynomial_filtered D
    (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) 1)
    (rough_native_stretched_lie_antitone 1 (by omega))
    (fun _ _ _ _ hv hw => rough_native_stretched_lie_bracket 1 (by omega) hv hw)
    (roughStretchedLowerCentralFiltration D.G 1)
    (fun j v hv => (rough_native_stretched_filtration_exp_mem_iff (I := D.I) 1 j v).mpr hv)
    _ (native_original_left_linear_log_weighted D g a)

end Hindman168

