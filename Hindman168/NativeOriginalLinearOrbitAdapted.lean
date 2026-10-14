import Hindman168.NativeOriginalLinearOrbitPolynomial
import Hindman168.RoughVectorCoefficientSubmodule

/-! Explicit coefficient and group-difference versions of adaptation to
the ORIGINAL lower central series; all original step bounds are retained. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_original_unstretched_group_layer {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (j : ℕ) :
    roughStretchedLowerCentralFiltration D.G 1 j = nilLowerCentralFiltration D.G j := by
  simp only [roughStretchedLowerCentralFiltration, ceilDiv_one]

theorem native_original_unstretched_lie_layer {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (j : ℕ) :
    roughNativeStretchedLieFiltration (I := D.I) (G := D.G) 1 j =
      nativeLieLowerCentralModel (I := D.I) (G := D.G) (j-1) := by
  simp only [roughNativeStretchedLieFiltration, ceilDiv_one]

theorem native_original_left_linear_coefficient_adapted {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (g a : D.G) (J : Unit →₀ ℕ) :
    roughVectorMvCoefficient (nativeOriginalLeftLinearLog D g a) J ∈
      nativeLieLowerCentralModel (I := D.I) (G := D.G) (J.sum (fun _ m => m)-1) := by
  have h := rough_vector_weighted_coefficient _ (rough_native_stretched_lie_antitone 1 (by omega))
    (native_original_left_linear_log_weighted D g a) J
  simpa only [Nat.add_zero, native_original_unstretched_lie_layer] using h

theorem native_original_left_linear_all_real_adapted {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (g a : D.G) :
    RoughFilteredPolynomial (nilLowerCentralFiltration D.G)
      (fun x : Unit → ℝ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (x () • nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) * a) := by
  intro hs x
  have he : (fun y : Unit → ℝ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) (nativeOriginalLeftLinearLog D g a) y)) =
      (fun y : Unit → ℝ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (y () • nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) * a) := by
    funext y
    rw [native_original_left_linear_log_eval, nativeLieExponential_globalLogarithm]
  have h := native_original_left_linear_real_filtered D g a hs x
  rw [he, native_original_unstretched_group_layer] at h
  exact h

theorem native_original_left_linear_integer_adapted {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (g a : D.G) :
    RoughFilteredPolynomial (nilLowerCentralFiltration D.G) (fun b : ℤ => g ^ b * a) := by
  let c : ℤ →+ (Unit → ℝ) := {
    toFun := fun b _ => (b : ℝ)
    map_zero' := by funext j; exact Int.cast_zero
    map_add' := by intro b d; funext j; exact Int.cast_add _ _ }
  have h := rough_filtered_polynomial_precompose _ _
    (native_original_left_linear_all_real_adapted D g a) c
  have he : (fun b : ℤ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      ((c b) () • nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) * a) =
      (fun b : ℤ => g ^ b * a) := by
    funext b
    change nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      ((b : ℝ) • nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) * a = _
    rw [nativeLieExponential_int_smul, nativeLieExponential_globalLogarithm]
  rwa [he] at h

end Hindman168
