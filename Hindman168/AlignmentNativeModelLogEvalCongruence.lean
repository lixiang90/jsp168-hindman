import Hindman168.AlignmentNativeModelLogPolynomial
import Hindman168.NativeNilmanifoldData

/-! Evaluations of the literal native model log polynomial depend only on
evaluations of its original exponent polynomials. This is an algebraic
congruence on ALL real inputs, with no integer-orbit or analytic hypothesis. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u

theorem alignment_native_model_log_eval_congr {σ θ : Type*} [Fintype σ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (n : ℕ) (v : Fin (n+1) → σ → ℤ)
    (g a : D.G) :
    letI : LieGroup D.I (minSmoothness ℝ 3) D.G := lieGroup_smooth_min_three
    ∀ (ell : alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra D.I D.G) →ₗ[ℝ] ℝ)
    (P : MvPolynomial θ ℝ) (Q : σ → MvPolynomial θ ℝ) (z w : θ → ℝ)
    (_ : MvPolynomial.eval z P=MvPolynomial.eval w P)
    (_ : ∀ e, MvPolynomial.eval z (Q e)=MvPolynomial.eval w (Q e)),
    MvPolynomial.eval z (alignmentNativeModelLogPolynomial (E := D.E) (I := D.I) (G := D.G) n v g a ell P Q)=
      MvPolynomial.eval w (alignmentNativeModelLogPolynomial (E := D.E) (I := D.I) (G := D.G) n v g a ell P Q) := by
  letI : LieGroup D.I (minSmoothness ℝ 3) D.G := lieGroup_smooth_min_three
  intro ell P Q z w hP hQ
  letI := nativeFiniteProductNormedAddCommGroup (E := D.E) n
  letI := nativeFiniteProductNormedSpace (E := D.E) n
  unfold alignmentNativeModelLogPolynomial alignmentNativeArrayLogPolynomial nativeFiniteOrbitLogProjection
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold nativeLieMultivariateOrbitLog
  rw [vectorPolynomialMultivariateProjection_eval,vectorPolynomialMultivariateProjection_eval]
  congr 2
  simp only [alignmentSelectedExponentPolynomial,map_add,map_sum,map_mul,MvPolynomial.eval_C,hP,hQ]

end Hindman168
