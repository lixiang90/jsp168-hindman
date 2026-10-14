import Hindman168.RoughFiniteCoefficientAssembly
import Hindman168.RoughModelBoxBounds

namespace Hindman168
open MvPolynomial

theorem roughProgressionPolynomial_map {κ R T : Type*} [CommSemiring R] [CommSemiring T]
    (f : R →+* T) (P : Polynomial R) :
    map f (roughProgressionPolynomial (κ := κ) P) =
      roughProgressionPolynomial (P.map f) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [roughProgressionPolynomial, Polynomial.eval₂_add, map_add, Polynomial.map_add] at *
    rw [hp, hq]
  | monomial n a =>
    simp only [roughProgressionPolynomial, Polynomial.eval₂_monomial,
      Polynomial.map_monomial, map_mul, map_C, map_pow, map_X]

theorem roughSpatialJointPolynomial_map {κ R T : Type*} [CommSemiring R] [CommSemiring T]
    (f : R →+* T) (s : Finset (κ →₀ ℕ)) (M0 : Polynomial R)
    (M : (κ →₀ ℕ) → Polynomial R) :
    map f (roughSpatialJointPolynomial s M0 M) =
      roughSpatialJointPolynomial s (M0.map f) (fun I => (M I).map f) := by
  simp only [roughSpatialJointPolynomial, map_add, map_sum, map_mul,
    roughProgressionPolynomial_map, map_rename, map_monomial, map_one]

theorem rough_joint_rational_real_section {κ : Type*}
    (s : Finset (κ →₀ ℕ)) (M0 : Polynomial ℚ) (M : (κ →₀ ℕ) → Polynomial ℚ)
    (z : ℕ) (x : κ → ℝ) :
    eval (Option.elim · (z : ℝ) x) (map (Rat.castHom ℝ) (roughSpatialJointPolynomial s M0 M)) =
      eval x (roughSpatialFixedPolynomial s (((M0.eval (z : ℚ) : ℚ) : ℝ))
        (fun I => (((M I).eval (z : ℚ) : ℚ) : ℝ))) := by
  rw [roughSpatialJointPolynomial_map, roughSpatialJointPolynomial_eval]
  have he : ∀ P : Polynomial ℚ,
      (P.map (Rat.castHom ℝ)).eval (z : ℝ) = ((P.eval (z : ℚ) : ℚ) : ℝ) := by
    intro P
    have h := Polynomial.eval_map_apply (p := P) (Rat.castHom ℝ) (z : ℚ)
    change (P.map (Rat.castHom ℝ)).eval ((z : ℚ) : ℝ) = ((P.eval (z : ℚ) : ℚ) : ℝ) at h
    simpa only [Rat.cast_natCast] using h
  simp only [he]

theorem rough_joint_horizontal_error_section {κ : Type*}
    (s : Finset (κ →₀ ℕ)) (P0 : Polynomial ℝ) (theta : (κ →₀ ℕ) → Polynomial ℝ)
    (M0 : Polynomial ℚ) (M : (κ →₀ ℕ) → Polynomial ℚ) (z : ℕ) (x : κ → ℝ) :
    eval (Option.elim · (z : ℝ) x)
      (roughSpatialJointPolynomial s P0 theta - map (Rat.castHom ℝ) (roughSpatialJointPolynomial s M0 M)) =
    eval x (roughErrorPolynomial s (P0.eval (z : ℝ) - (((M0.eval (z : ℚ) : ℚ) : ℝ)))
      (fun I => (theta I).eval (z : ℝ) - (((M I).eval (z : ℚ) : ℚ) : ℝ))) := by
  rw [map_sub, roughSpatialJointPolynomial_eval, rough_joint_rational_real_section]
  change eval x (roughErrorPolynomial s _ _) - eval x (roughErrorPolynomial s _ _) = _
  rw [← map_sub, ← rough_error_polynomial_sub]

theorem rough_joint_horizontal_error_box {κ : Type*} [Fintype κ]
    (s : Finset (κ →₀ ℕ)) (d : ℕ) (hd : ∀ I ∈ s, (∑ j, I j) ≤ d)
    {w H q z : ℕ} {Z A C : ℝ}
    (P0 : Polynomial ℝ) (theta : (κ →₀ ℕ) → Polynomial ℝ)
    (M0 : Polynomial ℚ) (M : (κ →₀ ℕ) → Polynomial ℚ)
    (hmodels : ∀ I ∈ s, RoughCoefficientModel w H q (∑ j, I j) Z A (theta I) (M I))
    (hz : z < H) (hA : 0 ≤ A) (hC : 1 ≤ C) (hZ : 0 < Z)
    (h0 : 0 ≤ P0.eval (z : ℝ) - (((M0.eval (z : ℚ) : ℚ) : ℝ)) ∧
      P0.eval (z : ℝ) - (((M0.eval (z : ℚ) : ℚ) : ℝ)) < 1)
    (x : κ → ℝ) (hx : ∀ j, |x j| ≤ C * Z) :
    |eval (Option.elim · (z : ℝ) x)
      (roughSpatialJointPolynomial s P0 theta - map (Rat.castHom ℝ) (roughSpatialJointPolynomial s M0 M))| ≤
      1 + (s.card : ℝ) * A * C ^ d := by
  rw [rough_joint_horizontal_error_section]
  exact (rough_model_box_bounds s d hd theta M hmodels hz hA hC hZ h0 x hx).1

end Hindman168
