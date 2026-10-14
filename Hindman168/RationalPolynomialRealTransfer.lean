import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Real.Basic

namespace Hindman168

theorem rationalPolynomial_real_degree {σ : Type*} (P : MvPolynomial σ ℚ) :
    (MvPolynomial.map (Rat.castHom ℝ) P).totalDegree ≤ P.totalDegree := by
  unfold MvPolynomial.totalDegree
  exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)

theorem rationalPolynomial_real_eval {σ : Type*} (P : MvPolynomial σ ℚ) (z : σ → ℚ) :
    MvPolynomial.eval (fun j => (z j : ℝ)) (MvPolynomial.map (Rat.castHom ℝ) P) =
      (MvPolynomial.eval z P : ℝ) := by
  rw [← MvPolynomial.eval₂_eq_eval_map]
  exact (MvPolynomial.hom_eval₂ P (RingHom.id ℚ) (Rat.castHom ℝ) z).symm

end Hindman168
