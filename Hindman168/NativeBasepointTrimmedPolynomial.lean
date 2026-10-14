import Hindman168.NativeBasepointPolynomial
import Hindman168.RoughNativeWeightedFilteredPolynomial
import Hindman168.RoughVectorZeroTrim
import Hindman168.RoughNativeStretchedLieTerminal

/-! Actual zero-trimmed original basepoint logarithmic polynomial. Its
ordinary degree is bounded by s*d, while genuine filteredness keeps the
SAME original stretch d and SAME original filtration degree. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeBasepointPolynomial {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (r : D.G) :
    RoughVectorMvPolynomial σ D.E := roughVectorMvZeroTrim (nativeBasepointRawPolynomial D p r)

theorem native_basepoint_polynomial_eval {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (r : D.G) (x : σ → ℝ) :
    roughVectorMvEval (E := D.E) (nativeBasepointPolynomial D p r) x =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (roughGroupBasepointNormalization
          (fun y : σ → ℝ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            (roughVectorMvEval (E := D.E) p y)) r x) := by
  rw [nativeBasepointPolynomial,rough_vector_zero_trim_eval,native_basepoint_raw_polynomial_eval]

theorem native_basepoint_polynomial_exp {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (r : D.G) (x : σ → ℝ) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) (nativeBasepointPolynomial D p r) x) =
      roughGroupBasepointNormalization
        (fun y : σ → ℝ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) p y)) r x := by
  rw [native_basepoint_polynomial_eval,nativeLieExponential_globalLogarithm]

theorem native_basepoint_polynomial_zero {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (r : D.G) :
    roughVectorMvEval (E := D.E) (nativeBasepointPolynomial D p r) 0 = 0 := by
  rw [native_basepoint_polynomial_eval,rough_group_basepoint_normalization_zero]
  exact nativeLieGlobalLogarithm_one (E := D.E) (I := D.I) (G := D.G)

theorem native_basepoint_polynomial_weighted {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial σ D.E) (hp : RoughVectorMvDegreeLE p d) (r : D.G) :
    RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d)
      (nativeBasepointPolynomial D p r) 0 :=
  rough_vector_zero_trim_weighted _ (native_basepoint_raw_polynomial_weighted D d hd p hp r)

theorem native_basepoint_polynomial_degree {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial σ D.E) (hp : RoughVectorMvDegreeLE p d) (r : D.G) :
    RoughVectorMvDegreeLE (nativeBasepointPolynomial D p r) (s*d) := by
  exact rough_vector_zero_trim_degree _ (rough_native_stretched_lie_antitone d hd)
    (native_basepoint_raw_polynomial_weighted D d hd p hp r)
    (rough_native_stretched_lie_terminal d hd D.step_le)

theorem native_basepoint_polynomial_filtered {s : ℕ} {σ : Type*} [Fintype σ]
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial σ D.E) (hp : RoughVectorMvDegreeLE p d) (r : D.G) :
    RoughFilteredPolynomial (roughStretchedLowerCentralFiltration D.G d)
      (fun x : σ → ℝ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) (nativeBasepointPolynomial D p r) x)) :=
  rough_native_weighted_log_polynomial_filtered d hd (native_basepoint_polynomial_weighted D d hd p hp r)

theorem native_basepoint_integer_polynomial_filtered {s : ℕ} {σ : Type*} [Fintype σ]
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial σ D.E) (hp : RoughVectorMvDegreeLE p d) (r : D.G) :
    RoughFilteredPolynomial (roughStretchedLowerCentralFiltration D.G d)
      (fun x : σ → ℤ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) (nativeBasepointPolynomial D p r) (fun j => (x j : ℝ)))) :=
  rough_native_integer_weighted_log_polynomial_filtered d hd (native_basepoint_polynomial_weighted D d hd p hp r)

end Hindman168
