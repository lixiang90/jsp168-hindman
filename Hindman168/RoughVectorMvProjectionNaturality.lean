import Hindman168.RoughVectorMvLinearMap

/-! Exact scalar polynomial and coefficient compatibility under actual
linear projection, stronger than equality on sampled points alone. -/

namespace Hindman168

theorem roughVectorMvProjection_linearMap {σ E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →ₗ[ℝ] F) (ell : F →ₗ[ℝ] ℝ) (p : RoughVectorMvPolynomial σ E) :
    roughVectorMvProjection ell (roughVectorMvLinearMap L p) =
      roughVectorMvProjection (ell.comp L) p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change a.1 * MvPolynomial.C (ell (L a.2)) +
      roughVectorMvProjection ell (roughVectorMvLinearMap L p) = _
    rw [ih]
    rfl

theorem roughVectorMvProjection_linearMap_coeff {σ E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →ₗ[ℝ] F) (ell : F →ₗ[ℝ] ℝ) (p : RoughVectorMvPolynomial σ E) (J : σ →₀ ℕ) :
    MvPolynomial.coeff J (roughVectorMvProjection ell (roughVectorMvLinearMap L p)) =
      MvPolynomial.coeff J (roughVectorMvProjection (ell.comp L) p) := by
  rw [roughVectorMvProjection_linearMap]

end Hindman168
