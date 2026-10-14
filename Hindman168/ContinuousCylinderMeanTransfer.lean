import Hindman168.ContinuousCylinderListRepresentation
import Hindman168.ComplexMeanObservableApproximation
import Hindman168.FiniteComplexCoefficientError

/-! Exact cylinder-list means and finite detectors for complete continuous tests.
Both empirical means retain their own original samples, maps and normalization.
Empty sample sets have zero mean. -/
namespace Hindman168
open FiniteMass
open scoped Classical
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

omit [CompactSpace X] in
theorem complex_expectation_cylinder_linear_combination {α : Type*}
    (μ : Mass α) (x : α → X) (l : List (ℂ × List C(X,ℂ))) :
    complexExpectation μ (fun a => continuousCylinderLinearCombination l (x a)) =
      (l.map (fun t => t.1*complexExpectation μ (fun a => t.2.prod (x a)))).sum := by
  induction l with
  | nil => simp [continuousCylinderLinearCombination,complexExpectation,Finsupp.sum]
  | cons t l ih =>
    have he : continuousCylinderLinearCombination (t::l)=
        t.1 • t.2.prod+continuousCylinderLinearCombination l := by
      simp only [continuousCylinderLinearCombination,List.map_cons,List.sum_cons]
    rw [he]
    have hlin : complexExpectation μ (fun a => (t.1 • t.2.prod+continuousCylinderLinearCombination l) (x a))=
        t.1*complexExpectation μ (fun a => t.2.prod (x a))+
        complexExpectation μ (fun a => continuousCylinderLinearCombination l (x a)) := by
      unfold complexExpectation Finsupp.sum
      simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    rw [hlin,ih,List.map_cons,List.sum_cons]

omit [CompactSpace X] in
theorem continuous_cylinder_two_mean_error {α β : Type*}
    (μ : Mass α) (ν : Mass β) (x : α → X) (y : β → X)
    (l : List (ℂ × List C(X,ℂ))) (ε R : ℝ) (hε : 0 < ε)
    (hsize : (l.map (fun t => ‖t.1‖)).sum < R)
    (hterms : ∀ t ∈ l, ‖complexExpectation μ (fun a => t.2.prod (x a))-
        complexExpectation ν (fun b => t.2.prod (y b))‖ ≤ ε) :
    ‖complexExpectation μ (fun a => continuousCylinderLinearCombination l (x a))-
      complexExpectation ν (fun b => continuousCylinderLinearCombination l (y b))‖ < R*ε := by
  rw [complex_expectation_cylinder_linear_combination,complex_expectation_cylinder_linear_combination,
    finite_complex_list_linear_difference]
  exact finite_complex_list_positive_budget l Prod.fst
    (fun t => complexExpectation μ (fun a => t.2.prod (x a))-
      complexExpectation ν (fun b => t.2.prod (y b))) ε R hε hsize hterms

theorem continuous_cylinder_approximant_detects {α β : Type*}
    (S : Finset α) (T : Finset β) (x : α → X) (y : β → X)
    (F : C(X,ℂ)) (l : List (ℂ × List C(X,ℂ))) (η R : ℝ)
    (hη : 0 < η) (hR : 0 < R)
    (hclose : ‖F-continuousCylinderLinearCombination l‖ < η/4)
    (hsize : (l.map (fun t => ‖t.1‖)).sum < R)
    (hbad : η ≤ ‖complexExpectation (uniformFinsetMass S) (fun a => F (x a))-
      complexExpectation (uniformFinsetMass T) (fun b => F (y b))‖) :
    ∃ t ∈ l, η/(2*R) ≤ ‖complexExpectation (uniformFinsetMass S) (fun a => t.2.prod (x a))-
      complexExpectation (uniformFinsetMass T) (fun b => t.2.prod (y b))‖ := by
  by_contra hn
  have ht : ∀ t ∈ l, ‖complexExpectation (uniformFinsetMass S) (fun a => t.2.prod (x a))-
      complexExpectation (uniformFinsetMass T) (fun b => t.2.prod (y b))‖ ≤ η/(2*R) := by
    intro t ht
    exact (lt_of_not_ge (fun h => hn ⟨t,ht,h⟩)).le
  have hsmall := continuous_cylinder_two_mean_error (uniformFinsetMass S) (uniformFinsetMass T)
    x y l (η/(2*R)) R (by positivity) hsize ht
  have he : R*(η/(2*R))=η/2 := by field_simp
  rw [he] at hsmall
  have hS := complex_uniform_mean_observable_difference S (fun a => F (x a))
    (fun a => continuousCylinderLinearCombination l (x a)) (η/4) (by positivity)
    (fun a _ => (ContinuousMap.norm_coe_le_norm (F-continuousCylinderLinearCombination l) (x a)).trans hclose.le)
  have hT := complex_uniform_mean_observable_difference T (fun b => F (y b))
    (fun b => continuousCylinderLinearCombination l (y b)) (η/4) (by positivity)
    (fun b _ => (ContinuousMap.norm_coe_le_norm (F-continuousCylinderLinearCombination l) (y b)).trans hclose.le)
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (complexExpectation (uniformFinsetMass S) (fun a => F (x a)))
    (complexExpectation (uniformFinsetMass S) (fun a => continuousCylinderLinearCombination l (x a)))
    (complexExpectation (uniformFinsetMass T) (fun b => F (y b)))
  have htri' := norm_sub_le_norm_sub_add_norm_sub
    (complexExpectation (uniformFinsetMass S) (fun a => continuousCylinderLinearCombination l (x a)))
    (complexExpectation (uniformFinsetMass T) (fun b => continuousCylinderLinearCombination l (y b)))
    (complexExpectation (uniformFinsetMass T) (fun b => F (y b)))
  rw [norm_sub_rev (complexExpectation (uniformFinsetMass T) (fun b => continuousCylinderLinearCombination l (y b)))] at htri'
  linarith

end Hindman168
