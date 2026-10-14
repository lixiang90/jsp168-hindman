import Hindman168.MvPolynomialBinomialExpansion

/-! The COMPLETE actual binomial coefficient table is unchanged when the
box bound is enlarged beyond the TRUE degree of the ORIGINAL polynomial. -/

namespace Hindman168
open scoped BigOperators
variable {σ : Type*} [Fintype σ]

theorem mv_binomial_box_mono {d e : ℕ} (hde : d ≤ e) : mvBinomialBox σ d ⊆ mvBinomialBox σ e := by
  intro J hJ
  exact (mv_binomial_box_mem e J).mpr (fun i => ((mv_binomial_box_mem d J).mp hJ i).trans hde)

theorem mv_binomial_coefficient_degree_extension (p : MvPolynomial σ ℝ) (d e : ℕ)
    (hde : d ≤ e) (hp : p.totalDegree ≤ d) (I : σ → ℕ) :
    mvPolynomialBinomialCoefficient p e I = mvPolynomialBinomialCoefficient p d I := by
  classical
  unfold mvPolynomialBinomialCoefficient
  symm
  apply Finset.sum_subset (mv_binomial_box_mono hde)
  intro J _ hJ
  have hn : ¬ ∀ i, J i ≤ d := fun h => hJ ((mv_binomial_box_mem d J).mpr h)
  push Not at hn
  obtain ⟨i,hi⟩ := hn
  have hWeight : d < ∑ j, J j :=
    hi.trans_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  rw [scalar_mv_coefficient_zero_above_degree p d hp J hWeight,zero_mul]

end Hindman168
