import Hindman168.FiniteComplexDenseMean

/-! Exact complex pair duplication and genuine normalized counting
Cauchy--Schwarz. No phase agreement or pointwise lower bound is assumed. -/
namespace Hindman168
open scoped BigOperators Classical

theorem finite_complex_set_mean_product {α β : Type*} (S : Finset α) (T : Finset β)
    (f : α → ℂ) (g : β → ℂ) :
    finiteComplexSetMean (S ×ˢ T) (fun p => f p.1*g p.2) =
      finiteComplexSetMean S f * finiteComplexSetMean T g := by
  unfold finiteComplexSetMean
  rw [Finset.sum_product,Finset.card_product,Nat.cast_mul,div_mul_div_comm,Finset.sum_mul_sum]

theorem finite_complex_set_mean_star {α : Type*} (S : Finset α) (f : α → ℂ) :
    finiteComplexSetMean S (fun x => star (f x)) = star (finiteComplexSetMean S f) := by
  simp only [finiteComplexSetMean, Complex.star_def, map_div₀, map_sum, map_natCast]

theorem finite_complex_set_mean_pair_square {α : Type*} (S : Finset α) (f : α → ℂ) :
    finiteComplexSetMean (S ×ˢ S) (fun p => f p.1*star (f p.2)) =
      finiteComplexSetMean S f * star (finiteComplexSetMean S f) := by
  rw [finite_complex_set_mean_product S S f (fun x => star (f x)),
    finite_complex_set_mean_star]

theorem finite_complex_set_mean_cauchy_square {α : Type*} (S : Finset α) (hS : S.Nonempty) (f : α → ℂ) :
    ‖finiteComplexSetMean S f‖^2 ≤ (∑ x ∈ S, ‖f x‖^2)/(S.card : ℝ) := by
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have he := congrArg norm (finiteComplexSetMean_mul_card S f)
  rw [norm_mul,Complex.norm_natCast] at he
  have hBound : ‖finiteComplexSetMean S f‖*(S.card : ℝ) ≤ ∑ x ∈ S, ‖f x‖ :=
    he.le.trans (norm_sum_le _ _)
  have hsq := (sq_le_sq₀ (mul_nonneg (norm_nonneg _) hc.le)
    (Finset.sum_nonneg (fun x _ => norm_nonneg (f x)))).mpr hBound
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S (fun x => ‖f x‖) (fun _ => (1 : ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hCS
  apply (le_div_iff₀ hc).mpr
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    _ = (‖finiteComplexSetMean S f‖*(S.card : ℝ))^2 := by ring
    _ ≤ (∑ x ∈ S, ‖f x‖)^2 := hsq
    _ ≤ _ := by simpa only [mul_comm] using hCS

theorem finite_complex_set_mean_energy {α : Type*} (S : Finset α) (hS : S.Nonempty) (f : α → ℂ) :
    ‖finiteComplexSetMean S f‖^2 ≤ ‖finiteComplexSetMean S (fun x => f x*star (f x))‖ := by
  have he : finiteComplexSetMean S (fun x => f x*star (f x)) =
      (((∑ x ∈ S, ‖f x‖^2)/(S.card : ℝ) : ℝ) : ℂ) := by
    simp only [finiteComplexSetMean,Complex.star_def,Complex.mul_conj',Complex.ofReal_div,
      Complex.ofReal_sum,Complex.ofReal_pow,Complex.ofReal_natCast]
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact finite_complex_set_mean_cauchy_square S hS f

end Hindman168
