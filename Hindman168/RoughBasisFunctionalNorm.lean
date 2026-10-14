import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace Hindman168
open scoped BigOperators

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def roughBasisOperatorNormBudget (b : Module.Basis ι ℝ E) : ℝ :=
  max ((Fintype.card ι : ℝ)*‖b.equivFunL.toContinuousLinearMap‖) 1

theorem rough_basis_operator_norm_budget_positive (b : Module.Basis ι ℝ E) :
    0 < roughBasisOperatorNormBudget b :=
  lt_of_lt_of_le zero_lt_one (le_max_right _ _)

theorem rough_basis_values_operator_norm (b : Module.Basis ι ℝ E)
    (M : ℝ) (hM : 0 ≤ M) (χ : E →L[ℝ] ℝ) (hv : ∀ i, |χ (b i)| ≤ M) :
    ‖χ‖ ≤ roughBasisOperatorNormBudget b*M := by
  have hn := b.opNorm_le (u := χ) hM (fun i => by simpa only [Real.norm_eq_abs] using hv i)
  calc
    ‖χ‖ ≤ ((Fintype.card ι : ℝ)*‖b.equivFunL.toContinuousLinearMap‖)*M := by
      simpa only [nsmul_eq_mul] using hn
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hM

omit [Fintype ι] in
theorem rough_basis_horizontal_values_bound (b : Module.Basis ι ℝ E)
    (S : Finset ι) (L : Submodule ℝ E) (hL : ∀ i, i ∉ S → b i ∈ L)
    (χ : E →ₗ[ℝ] ℝ) (hχ : L ≤ χ.ker) (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ i ∈ S, |χ (b i)| ≤ M) : ∀ i, |χ (b i)| ≤ M := by
  intro i
  by_cases hi : i ∈ S
  · exact hv i hi
  · have hz : χ (b i) = 0 := hχ (hL i hi)
    simpa only [hz, abs_zero] using hM

omit [Fintype ι] in
theorem rough_basis_horizontal_integer_square_values_bound (b : Module.Basis ι ℝ E)
    (S : Finset ι) (L : Submodule ℝ E) (hL : ∀ i, i ∉ S → b i ∈ L)
    (χ : E →ₗ[ℝ] ℝ) (hχ : L ≤ χ.ker) (m : ι → ℤ)
    (hm : ∀ i ∈ S, χ (b i) = (m i : ℝ)) (M : ℝ) (hM : 0 ≤ M)
    (hsize : ∑ i ∈ S, (m i : ℝ)^2 ≤ M^2) : ∀ i, |χ (b i)| ≤ M := by
  apply rough_basis_horizontal_values_bound b S L hL χ hχ M hM
  intro i hi
  have hs : (m i : ℝ)^2 ≤ ∑ j ∈ S, (m j : ℝ)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (m j : ℝ)) hi
  rw [hm i hi]
  have ha := sq_abs (m i : ℝ)
  have hab := abs_nonneg (m i : ℝ)
  nlinarith

theorem rough_basis_horizontal_integer_square_operator_norm (b : Module.Basis ι ℝ E)
    (S : Finset ι) (L : Submodule ℝ E) (hL : ∀ i, i ∉ S → b i ∈ L)
    (χ : E →L[ℝ] ℝ) (hχ : L ≤ χ.toLinearMap.ker) (m : ι → ℤ)
    (hm : ∀ i ∈ S, χ (b i) = (m i : ℝ)) (M : ℝ) (hM : 0 ≤ M)
    (hsize : ∑ i ∈ S, (m i : ℝ)^2 ≤ M^2) :
    ‖χ‖ ≤ roughBasisOperatorNormBudget b*M :=
  rough_basis_values_operator_norm b M hM χ
    (rough_basis_horizontal_integer_square_values_bound b S L hL χ.toLinearMap hχ m hm M hM hsize)

end Hindman168
