import Hindman168.RoughSlowPolynomialOscillation
import Hindman168.RoughJointHorizontalError

namespace Hindman168
open MvPolynomial

theorem rough_joint_slow_subbox_oscillation {κ : Type*} [Fintype κ]
    (s : Finset (κ →₀ ℕ)) (d : ℕ) (hd : ∀ J ∈ s, (∑ j, J j) ≤ d)
    {w H q z : ℕ} {Z A C δ : ℝ}
    (P0 : Polynomial ℝ) (theta : (κ →₀ ℕ) → Polynomial ℝ)
    (M0 : Polynomial ℚ) (M : (κ →₀ ℕ) → Polynomial ℚ)
    (hmodels : ∀ J ∈ s, RoughCoefficientModel w H q (∑ j, J j) Z A (theta J) (M J))
    (hz : z < H) (hA : 0 ≤ A) (hC : 1 ≤ C) (hZ : 0 < Z) (hδ : 0 ≤ δ)
    (x y : κ → ℝ) (hx : ∀ j, |x j| ≤ C * Z) (hy : ∀ j, |y j| ≤ C * Z)
    (hxy : ∀ j, |x j - y j| ≤ δ * Z) :
    let a := roughSpatialJointPolynomial s P0 theta -
      map (Rat.castHom ℝ) (roughSpatialJointPolynomial s M0 M)
    |eval (Option.elim · (z : ℝ) x) a - eval (Option.elim · (z : ℝ) y) a| ≤
      (s.card : ℝ) * d * A * C ^ d * δ := by
  dsimp only
  rw [rough_joint_horizontal_error_section, rough_joint_horizontal_error_section]
  exact rough_error_polynomial_subbox_oscillation s d hd _ _ x y hA hC hZ hδ
    (fun J hJ => ((hmodels J hJ).2.2 z hz).2) hx hy hxy

end Hindman168
