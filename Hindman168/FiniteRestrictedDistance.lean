import Hindman168.FiniteEventPairLaw
import Hindman168.FiniteMixture

/-! L1 comparison under a common finite restriction and scalar. Signed
masses are allowed; no probability normalization is needed. -/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem distance_triangle {α : Type*} (μ ν ρ : Mass α) :
    distance μ ρ ≤ distance μ ν + distance ν ρ := by
  have he : μ - ρ = (μ - ν) + (ν - ρ) := by abel
  unfold distance
  rw [he]
  exact variation_add _ _

theorem distance_common_smul {α : Type*} (c : ℝ) (μ ν : Mass α) :
    distance (c • μ) (c • ν) = |c| * distance μ ν := by
  unfold distance
  rw [← smul_sub, variation_smul]

theorem distance_restricted_le {α : Type*} (μ ν : Mass α) (E : α → Prop) :
    distance (restrictedMass μ E) (restrictedMass ν E) ≤ distance μ ν := by
  let S := μ.support ∪ ν.support
  have hr (ρ : Mass α) : (restrictedMass ρ E).support ⊆ ρ.support := by
    intro x hx
    exact ((mem_restrictedMass_support ρ E x).mp hx).1
  have hl : (restrictedMass μ E - restrictedMass ν E).support ⊆ S :=
    Finsupp.support_sub.trans (Finset.union_subset_union (hr μ) (hr ν))
  have hh : (μ - ν).support ⊆ S := Finsupp.support_sub
  rw [distance, variation_eq_sum _ hl, distance, variation_eq_sum _ hh]
  apply Finset.sum_le_sum
  intro x _
  simp only [Finsupp.sub_apply, restrictedMass_apply]
  split_ifs
  · exact le_rfl
  · simp only [sub_self, abs_zero]
    exact abs_nonneg _

theorem distance_scaled_restricted_le {α : Type*} (μ ν : Mass α) (E : α → Prop)
    (c : ℝ) (hc : 0 ≤ c) :
    distance (c • restrictedMass μ E) (c • restrictedMass ν E) ≤ c * distance μ ν := by
  rw [distance_common_smul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (distance_restricted_le μ ν E) hc

end Hindman168.FiniteMass
