import Hindman168.RoughVectorCoefficientSubmodule
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-! Canonical aggregated monomial collection of the ACTUAL original vector
polynomial. Cancellation between original list terms is fully retained. -/

namespace Hindman168
open scoped BigOperators Classical
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def roughVectorMvSupport (p : RoughVectorMvPolynomial σ E) : Finset (σ →₀ ℕ) :=
  p.foldr (fun a S => a.1.support ∪ S) ∅

noncomputable def roughVectorMvCollect (p : RoughVectorMvPolynomial σ E) : RoughVectorMvPolynomial σ E :=
  (roughVectorMvSupport p).toList.map (fun J => (MvPolynomial.monomial J 1,roughVectorMvCoefficient p J))

theorem rough_vector_coefficient_zero_outside_support (p : RoughVectorMvPolynomial σ E)
    (J : σ →₀ ℕ) (hJ : J ∉ roughVectorMvSupport p) : roughVectorMvCoefficient p J = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      have hn : J ∉ a.1.support ∧ J ∉ roughVectorMvSupport p := by
        simpa only [roughVectorMvSupport,List.foldr_cons,Finset.mem_union,not_or] using hJ
      change MvPolynomial.coeff J a.1 • a.2 + roughVectorMvCoefficient p J = 0
      have hz : MvPolynomial.coeff J a.1 = 0 := by
        simpa only [MvPolynomial.mem_support_iff,not_not] using hn.1
      rw [hz,zero_smul,zero_add,ih hn.2]

theorem rough_vector_collect_projection (ell : E →ₗ[ℝ] ℝ) (p : RoughVectorMvPolynomial σ E) :
    roughVectorMvProjection ell (roughVectorMvCollect p) = roughVectorMvProjection ell p := by
  have he : ∀ L : List (σ →₀ ℕ), roughVectorMvProjection ell
      (L.map (fun J => (MvPolynomial.monomial J 1,roughVectorMvCoefficient p J))) =
      (L.map (fun J => MvPolynomial.monomial J (ell (roughVectorMvCoefficient p J)))).sum := by
    intro L
    induction L with
    | nil => rfl
    | cons J L ih =>
        simp only [List.map_cons,List.sum_cons,roughVectorMvProjection,ih]
        congr 1
        change MvPolynomial.monomial J 1 * MvPolynomial.monomial 0
          (ell (roughVectorMvCoefficient p J)) = _
        rw [MvPolynomial.monomial_mul,add_zero,one_mul]
  unfold roughVectorMvCollect
  rw [he,Finset.sum_map_toList]
  apply MvPolynomial.ext
  intro J
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  by_cases hJ : J ∈ roughVectorMvSupport p
  · rw [Finset.sum_ite_eq',if_pos hJ,rough_vector_coefficient_projection]
  · rw [Finset.sum_ite_eq',if_neg hJ]
    rw [← rough_vector_coefficient_projection,rough_vector_coefficient_zero_outside_support p J hJ,map_zero]

theorem rough_vector_collect_eval (p : RoughVectorMvPolynomial σ E) (x : σ → ℝ) :
    roughVectorMvEval (roughVectorMvCollect p) x = roughVectorMvEval p x := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℝ
    (roughVectorMvEval (roughVectorMvCollect p) x-roughVectorMvEval p x)).mp
  intro ell
  rw [map_sub,← roughVectorMvProjection_eval,← roughVectorMvProjection_eval,
    rough_vector_collect_projection,sub_self]

theorem rough_vector_collect_coefficient (p : RoughVectorMvPolynomial σ E) (J : σ →₀ ℕ) :
    roughVectorMvCoefficient (roughVectorMvCollect p) J = roughVectorMvCoefficient p J := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℝ
    (roughVectorMvCoefficient (roughVectorMvCollect p) J-roughVectorMvCoefficient p J)).mp
  intro ell
  rw [map_sub,rough_vector_coefficient_projection,rough_vector_coefficient_projection,
    rough_vector_collect_projection,sub_self]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem rough_vector_support_degree {p : RoughVectorMvPolynomial σ E} {d : ℕ}
    (hp : RoughVectorMvDegreeLE p d) (J : σ →₀ ℕ) (hJ : J ∈ roughVectorMvSupport p) :
    J.sum (fun _ n => n) ≤ d := by
  induction p with
  | nil => simp [roughVectorMvSupport] at hJ
  | cons a p ih =>
      have hm : J ∈ a.1.support ∨ J ∈ roughVectorMvSupport p := by
        simpa only [roughVectorMvSupport,List.foldr_cons,Finset.mem_union] using hJ
      rcases hm with ha | ht
      · exact (MvPolynomial.le_totalDegree ha).trans (hp a List.mem_cons_self)
      · exact ih (fun b hb => hp b (List.mem_cons_of_mem _ hb)) ht

theorem rough_vector_collect_degree {p : RoughVectorMvPolynomial σ E} {d : ℕ}
    (hp : RoughVectorMvDegreeLE p d) : RoughVectorMvDegreeLE (roughVectorMvCollect p) d := by
  rintro a ha
  obtain ⟨J,hJ,rfl⟩ := List.mem_map.mp ha
  exact (MvPolynomial.totalDegree_monomial_le J (1 : ℝ)).trans
    (rough_vector_support_degree hp J (Finset.mem_toList.mp hJ))

theorem rough_vector_collect_weighted (F : ℕ → Submodule ℝ E) (hF : Antitone F)
    {p : RoughVectorMvPolynomial σ E} {k : ℕ} (hp : RoughVectorMvWeightedDegree F p k) :
    RoughVectorMvWeightedDegree F (roughVectorMvCollect p) k := by
  rintro a ha
  obtain ⟨J,_,rfl⟩ := List.mem_map.mp ha
  rw [MvPolynomial.totalDegree_monomial J one_ne_zero]
  exact rough_vector_weighted_coefficient F hF hp J

end Hindman168
