import Hindman168.AlignmentExposedArrayOffsets
import Mathlib.Algebra.MvPolynomial.Degrees

namespace Hindman168
open scoped BigOperators Classical
open MvPolynomial

noncomputable def alignmentPolynomialInputShift {σ : Type*} (v : σ → ℤ)
    (p : MvPolynomial σ ℤ) : MvPolynomial σ ℤ :=
  eval₂Hom C (fun j => X j + C (v j)) p

theorem alignmentPolynomialInputShift_eval {σ : Type*} (v u : σ → ℤ)
    (p : MvPolynomial σ ℤ) :
    eval u (alignmentPolynomialInputShift v p) = eval (u + v) p := by
  unfold alignmentPolynomialInputShift
  change eval u (eval₂ C (fun j => X j + C (v j)) p) = eval (u + v) p
  rw [← eval_assoc]
  have hvars : (fun j => eval u (X j + C (v j))) = u + v := by
    funext j
    simp only [map_add, eval_X, eval_C, Pi.add_apply]
  change eval (fun j => eval u (X j + C (v j))) p = eval (u + v) p
  rw [hvars]

theorem alignmentPolynomial_linear_substitution_degree {σ τ : Type*}
    (f : σ → MvPolynomial τ ℤ) (hf : ∀ j, (f j).totalDegree ≤ 1)
    (p : MvPolynomial σ ℤ) : (eval₂Hom C f p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => arg 1; rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  rw [eval₂Hom_monomial]
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  change (∏ j ∈ d.support, f j ^ d j).totalDegree ≤ p.totalDegree
  apply (totalDegree_finsetProd _ _).trans
  calc
    ∑ j ∈ d.support, (f j ^ d j).totalDegree ≤ ∑ j ∈ d.support, d j := by
      apply Finset.sum_le_sum
      intro j _
      exact (totalDegree_pow _ _).trans (by simpa only [mul_one] using Nat.mul_le_mul_left (d j) (hf j))
    _ ≤ p.totalDegree := le_totalDegree hd

theorem alignmentPolynomialInputShift_degree {σ : Type*} (v : σ → ℤ)
    (p : MvPolynomial σ ℤ) : (alignmentPolynomialInputShift v p).totalDegree ≤ p.totalDegree := by
  apply alignmentPolynomial_linear_substitution_degree
  intro j
  exact (totalDegree_add _ _).trans (by rw [totalDegree_X, totalDegree_C]; exact le_rfl)

noncomputable def alignmentAffineArrayPolynomial {σ : Type*} [Fintype σ]
    (k : ℤ) (Δ : σ → ℤ) : MvPolynomial σ ℤ :=
  C k + ∑ j, C (Δ j) * X j

theorem alignmentAffineArrayPolynomial_eval {σ : Type*} [Fintype σ]
    (k : ℤ) (Δ u : σ → ℤ) :
    eval u (alignmentAffineArrayPolynomial k Δ) = k + ∑ j, u j * Δ j := by
  simp only [alignmentAffineArrayPolynomial, map_add, eval_C, map_sum, map_mul, eval_X]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem alignmentAffineArrayPolynomial_degree {σ : Type*} [Fintype σ]
    (k : ℤ) (Δ : σ → ℤ) : (alignmentAffineArrayPolynomial k Δ).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · rw [totalDegree_C]; exact Nat.zero_le _
  · apply totalDegree_finsetSum_le
    intro j _
    exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])

end Hindman168
