import Hindman168.RoughSlowPolynomial
import Hindman168.RoughDescentModels

namespace Hindman168
open scoped BigOperators

theorem rough_model_box_bounds {κ : Type*} [Fintype κ]
    (s : Finset (κ →₀ ℕ)) (d : ℕ) (hd : ∀ I ∈ s, (∑ j, I j) ≤ d)
    {w H q z : ℕ} {Z A C a0 : ℝ}
    (theta : (κ →₀ ℕ) → Polynomial ℝ) (M : (κ →₀ ℕ) → Polynomial ℚ)
    (hmodels : ∀ I ∈ s, RoughCoefficientModel w H q (∑ j, I j) Z A (theta I) (M I))
    (hz : z < H) (hA : 0 ≤ A) (hC : 1 ≤ C) (hZ : 0 < Z) (h0 : 0 ≤ a0 ∧ a0 < 1)
    (x : κ → ℝ) (hx : ∀ j, |x j| ≤ C * Z) :
    let E := roughErrorPolynomial s a0 (fun I =>
      (theta I).eval (z : ℝ) - (((M I).eval (z : ℚ) : ℚ) : ℝ))
    |MvPolynomial.eval x E| ≤ 1 + (s.card : ℝ) * A * C ^ d ∧
      ∀ j, |MvPolynomial.eval x (MvPolynomial.pderiv j E)| ≤
        ((s.card : ℝ) * d * A * C ^ d) * Z⁻¹ := by
  apply rough_error_polynomial_box_bounds s d hd a0 _ x hA hC hZ
  · rw [abs_of_nonneg h0.1]
    exact h0.2.le
  · intro I hI
    exact ((hmodels I hI).2.2 z hz).2
  · exact hx

theorem rough_error_polynomial_sub {κ : Type*} (s : Finset (κ →₀ ℕ))
    (a0 b0 : ℝ) (a b : (κ →₀ ℕ) → ℝ) :
    roughErrorPolynomial s (a0 - b0) (fun I => a I - b I) =
      roughErrorPolynomial s a0 a - roughErrorPolynomial s b0 b := by
  simp only [roughErrorPolynomial, map_sub, Finset.sum_sub_distrib]
  abel

end Hindman168
