import Hindman168.TensorProbability

/-!
# The sum of coordinate errors for products of probability laws

The comparison factors in this module really are probabilities. The
unnormalized harmonic comparisons continue to use FiniteTensor's mass
factors, rather than this specialization.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators

theorem tensorError_probability {α : Type*} (P : List (Mass α × Mass α)) :
    (∀ p ∈ P, (∀ a, 0 ≤ p.1 a) ∧ total p.1 = 1 ∧
      (∀ a, 0 ≤ p.2 a) ∧ total p.2 = 1) →
    tensorError P = (P.map (fun p => distance p.1 p.2)).sum := by
  classical
  induction P with
  | nil => intro _; rfl
  | cons p P ih =>
    intro h
    rcases p with ⟨μ, ν⟩
    obtain ⟨_, _, hν, htν⟩ := h (μ, ν) List.mem_cons_self
    have htail := fun q hq => h q (List.mem_cons_of_mem (μ, ν) hq)
    have htailnonneg : ∀ a, 0 ≤ tensorList (P.map Prod.fst) a := by
      apply tensorList_nonneg
      intro ρ hρ
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hρ
      exact (htail q hq).1
    have htailtotal : total (tensorList (P.map Prod.fst)) = 1 := by
      apply tensorList_total_one
      intro ρ hρ
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hρ
      exact (htail q hq).2.1
    have htv : ((P.map Prod.fst).map variation).prod = 1 := by
      rw [← tensorList_variation, variation_eq_total _ htailnonneg, htailtotal]
    simp only [tensorError, htv, variation_eq_total ν hν, htν, mul_one, one_mul,
      List.map_cons, List.sum_cons, ih htail]

theorem tensorList_probability_distance_sum {α : Type*} (P : List (Mass α × Mass α))
    (h : ∀ p ∈ P, (∀ a, 0 ≤ p.1 a) ∧ total p.1 = 1 ∧
      (∀ a, 0 ≤ p.2 a) ∧ total p.2 = 1) :
    distance (tensorList (P.map Prod.fst)) (tensorList (P.map Prod.snd)) ≤
      (P.map (fun p => distance p.1 p.2)).sum :=
  (tensorList_distance P).trans_eq (tensorError_probability P h)

theorem tensorList_probability_distance_caps {α : Type*} (P : List (Mass α × Mass α))
    (e : Mass α × Mass α → ℝ)
    (h : ∀ p ∈ P, (∀ a, 0 ≤ p.1 a) ∧ total p.1 = 1 ∧
      (∀ a, 0 ≤ p.2 a) ∧ total p.2 = 1)
    (he : ∀ p ∈ P, distance p.1 p.2 ≤ e p) :
    distance (tensorList (P.map Prod.fst)) (tensorList (P.map Prod.snd)) ≤ (P.map e).sum := by
  apply (tensorList_probability_distance_sum P h).trans
  induction P with
  | nil => rfl
  | cons p P ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (he p List.mem_cons_self)
      (ih (fun q hq => h q (List.mem_cons_of_mem p hq))
        (fun q hq => he q (List.mem_cons_of_mem p hq)))

end Hindman168.FiniteMass
