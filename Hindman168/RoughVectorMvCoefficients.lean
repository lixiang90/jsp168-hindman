import Hindman168.RoughVectorWeightedDegree
import Hindman168.RoughVectorMvLinearMap

/-! ACTUAL aggregated vector monomial coefficients. Scalar projections
recover precisely these coefficients, including cancellation between the
original list terms. No individual-term submodule membership is inferred. -/

namespace Hindman168
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def roughVectorMvCoefficient (p : RoughVectorMvPolynomial σ E) (J : σ →₀ ℕ) : E :=
  (p.map (fun a => MvPolynomial.coeff J a.1 • a.2)).sum

theorem rough_vector_coefficient_append (p q : RoughVectorMvPolynomial σ E) (J : σ →₀ ℕ) :
    roughVectorMvCoefficient (p++q) J = roughVectorMvCoefficient p J + roughVectorMvCoefficient q J := by
  simp only [roughVectorMvCoefficient,List.map_append,List.sum_append]

theorem rough_vector_coefficient_projection (ell : E →ₗ[ℝ] ℝ)
    (p : RoughVectorMvPolynomial σ E) (J : σ →₀ ℕ) :
    ell (roughVectorMvCoefficient p J) = MvPolynomial.coeff J (roughVectorMvProjection ell p) := by
  induction p with
  | nil => simp only [roughVectorMvCoefficient,List.map_nil,List.sum_nil,map_zero,
      roughVectorMvProjection,MvPolynomial.coeff_zero]
  | cons a p ih =>
      change ell (MvPolynomial.coeff J a.1 • a.2 + roughVectorMvCoefficient p J) =
        MvPolynomial.coeff J (a.1 * MvPolynomial.C (ell a.2) + roughVectorMvProjection ell p)
      rw [map_add,map_smul,MvPolynomial.coeff_add,
        mul_comm a.1 (MvPolynomial.C (ell a.2)),MvPolynomial.coeff_C_mul,ih]
      simp only [smul_eq_mul,mul_comm]

theorem rough_vector_coefficient_linear_map {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →ₗ[ℝ] F) (p : RoughVectorMvPolynomial σ E) (J : σ →₀ ℕ) :
    roughVectorMvCoefficient (roughVectorMvLinearMap L p) J = L (roughVectorMvCoefficient p J) := by
  induction p with
  | nil => simp only [roughVectorMvLinearMap,roughVectorMvCoefficient,List.map_nil,List.sum_nil,map_zero]
  | cons a p ih =>
      change MvPolynomial.coeff J a.1 • L a.2 +
        roughVectorMvCoefficient (roughVectorMvLinearMap L p) J = _
      rw [ih]
      simp only [roughVectorMvCoefficient,List.map_cons,List.sum_cons,map_add,map_smul]

end Hindman168
