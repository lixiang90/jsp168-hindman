import Hindman168.FinitePiProductLinearApproximation
import Hindman168.FiniteComplexMassMean

/-! Exact original finite-mass means of finite product combinations. Actual
coefficients are retained, allowing a common coefficient budget to transfer
original product face errors to complete continuous cube test approximants. -/
namespace Hindman168
open FiniteMass
open scoped BigOperators Classical
variable {ι α : Type*} [Fintype ι] (X : ι → Type*) [∀ i, MetricSpace (X i)]

omit [Fintype ι] in
theorem complex_expectation_continuous_affine_combination (μ : Mass α) (x : α → ∀ i, X i)
    (c : ℂ) (F G : C((∀ i, X i),ℂ)) :
    complexExpectation μ (fun a => (c • F+G) (x a))=
      c*complexExpectation μ (fun a => F (x a))+complexExpectation μ (fun a => G (x a)) := by
  unfold complexExpectation Finsupp.sum
  simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  ring

theorem complex_expectation_finite_pi_product_linear_combination
    (μ : Mass α) (x : α → ∀ i, X i) (l : List (ℂ × (∀ i, C(X i,ℂ)))) :
    complexExpectation μ (fun a => finitePiProductLinearCombination X l (x a))=
      (l.map (fun t => t.1*complexExpectation μ (fun a => finitePiComplexProduct X t.2 (x a)))).sum := by
  induction l with
  | nil => simp [finitePiProductLinearCombination,complexExpectation,Finsupp.sum]
  | cons t l ih =>
    have he : finitePiProductLinearCombination X (t::l)=
        t.1 • finitePiComplexProduct X t.2+finitePiProductLinearCombination X l := by
      simp only [finitePiProductLinearCombination,List.map_cons,List.sum_cons]
    rw [he,complex_expectation_continuous_affine_combination,ih,List.map_cons,List.sum_cons]

end Hindman168
