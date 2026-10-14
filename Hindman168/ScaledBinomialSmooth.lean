import Hindman168.AdaptedTaylorBinomial
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Exact scaled binomial polynomials and their jointly smooth parameter
family, including the limit at inverse length zero. No coefficient limit
or smooth-factor bound is assumed. -/
namespace Hindman168
open scoped BigOperators ContDiff

noncomputable def scaledBinomialSmooth (j : ℕ) (z t b : ℝ) : ℝ :=
  z * (j.factorial : ℝ)⁻¹ * ∏ r ∈ Finset.range j, (b - (r : ℝ)*t)

theorem scaled_binomial_smooth_zero (j : ℕ) (z b : ℝ) :
    scaledBinomialSmooth j z 0 b = z * (j.factorial : ℝ)⁻¹ * b^j := by
  simp only [scaledBinomialSmooth, mul_zero, sub_zero, Finset.prod_const, Finset.card_range]

theorem scaled_binomial_smooth_identity (j : ℕ) (epsilon L b : ℝ) (hL : L ≠ 0) :
    epsilon * MvPolynomial.eval (fun _ => L*b) (adaptedTaylorBinomial j) =
      scaledBinomialSmooth j (L^j * epsilon) L⁻¹ b := by
  have he (r : ℕ) : L*b - (r : ℝ) = L*(b-(r : ℝ)*L⁻¹) := by
    field_simp [hL]
  have hp : (∏ r ∈ Finset.range j, (L*b - (r : ℝ))) =
      L^j * ∏ r ∈ Finset.range j, (b-(r : ℝ)*L⁻¹) := by
    simp_rw [he]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_range]
  simp only [adaptedTaylorBinomial, map_mul, MvPolynomial.eval_C, map_prod, map_sub,
    MvPolynomial.eval_X]
  rw [hp]
  unfold scaledBinomialSmooth
  ring

theorem scaled_binomial_smooth_identity_all_lengths (j : ℕ) (epsilon L b : ℝ) :
    epsilon * MvPolynomial.eval (fun _ => L*b) (adaptedTaylorBinomial j) =
      scaledBinomialSmooth j (L^j * epsilon) L⁻¹ b := by
  by_cases hL : L = 0
  · subst L
    by_cases hj : j = 0
    · subst j
      simp [adaptedTaylorBinomial, scaledBinomialSmooth]
    · have hjPos : 0 < j := by omega
      have hb : MvPolynomial.eval (fun _ => (0 : ℝ)) (adaptedTaylorBinomial j) = 0 := by
        simpa only [Nat.cast_zero, Nat.choose_eq_zero_of_lt hjPos] using adapted_taylor_binomial_eval_nat j 0
      simp only [zero_mul, hb, mul_zero, zero_pow hj, scaledBinomialSmooth]
  · exact scaled_binomial_smooth_identity j epsilon L b hL

theorem scaled_binomial_smooth_contDiff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (j : ℕ) (z t b : X → ℝ) (hz : ContDiff ℝ ∞ z) (ht : ContDiff ℝ ∞ t) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (fun x => scaledBinomialSmooth j (z x) (t x) (b x)) := by
  unfold scaledBinomialSmooth
  apply (hz.mul contDiff_const).mul
  apply contDiff_prod
  intro r _
  exact hb.sub (contDiff_const.mul ht)

end Hindman168
