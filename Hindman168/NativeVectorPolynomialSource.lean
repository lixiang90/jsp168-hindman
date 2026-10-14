import Hindman168.NativeNilmanifoldData
import Hindman168.RoughVectorMvCoordinates
import Hindman168.NativeResidualSource

/-! Actual native exponential extension of a finite vector polynomial.
The all-real log identity is proved, and coordinate identities force exact
agreement with specified original group samples. -/
namespace Hindman168
open Module
open scoped Manifold ContDiff BigOperators
universe u

noncomputable def nativeVectorPolynomialSource {σ : Type*} {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) :
    (σ → ℝ) → D.G := by
  letI : LieGroup D.I (minSmoothness ℝ 3) D.G := lieGroup_smooth_min_three
  exact fun x => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
    (roughVectorMvEval p x : D.E)

theorem native_vector_polynomial_source_log {σ : Type*} {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (x : σ → ℝ) :
    nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (nativeVectorPolynomialSource D p x) = roughVectorMvEval p x := by
  exact nativeLieGlobalLogarithm_exponential (E := D.E) (I := D.I) (G := D.G) _

theorem native_vector_polynomial_source_sample {σ : Type*} {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E)
    (x : σ → ℝ) (a : D.G)
    (h : roughVectorMvEval p x=nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) a) :
    nativeVectorPolynomialSource D p x=a := by
  unfold nativeVectorPolynomialSource
  rw [h]
  exact nativeLieExponential_globalLogarithm (E := D.E) (I := D.I) (G := D.G) a

theorem native_basis_polynomial_source_sample {σ : Type*} {s r : ℕ}
    (D : NativeNilmanifoldData.{u} s) (b : Basis (Fin r) ℝ D.E)
    (p : Fin r → MvPolynomial σ ℝ) (x : σ → ℝ) (a : D.G)
    (h : ∀ i, MvPolynomial.eval x (p i) =
      b.repr (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) a) i) :
    nativeVectorPolynomialSource D (roughVectorMvFromBasis b p) x=a := by
  apply native_vector_polynomial_source_sample
  rw [roughVectorMvFromBasis_eval]
  simp_rw [h]
  exact b.sum_repr _

theorem native_vector_polynomial_residual_log {κ : Type*} {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial (Option κ) D.E)
    (a : κ → ℤ) (q : ℕ) :
    ∀ (z : ℝ) (y : κ → ℝ),
      roughVectorMvEval (roughNativeResidualPolynomial p a q) (Option.elim · z y) =
        nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
          (roughNativeResidualSource D (nativeVectorPolynomialSource D p) a q (Option.elim · z y)) :=
  rough_native_residual_source_log D _ p a q (fun _ _ => (native_vector_polynomial_source_log D p _).symm)

end Hindman168
