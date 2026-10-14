import Hindman168.ConditionalRoughCoprimality
import Hindman168.UniformFiniteMass

/-! Positive coefficient bounds give uniform domination after conditioning
on any nonempty finite set. The original event denominator is retained. -/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem event_finset_mem {α : Type*} (μ : Mass α) (S : Finset α) :
    event μ (fun x => x ∈ S) = ∑ x ∈ S, μ x := by
  classical
  rw [event_eq_sum μ _ (Finset.Subset.refl _)]
  trans ∑ x ∈ μ.support.filter (fun x => x ∈ S), μ x
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> rfl
  apply Finset.sum_subset
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x hx hnot
    have ho : x ∉ μ.support := by
      intro hs
      exact hnot (Finset.mem_filter.mpr ⟨hs, hx⟩)
    exact Finsupp.notMem_support_iff.mp ho

theorem event_finset_mem_lower {α : Type*} (μ : Mass α) (S : Finset α) {b : ℝ}
    (hlo : ∀ x ∈ S, b ≤ μ x) :
    (S.card : ℝ) * b ≤ event μ (fun x => x ∈ S) := by
  rw [event_finset_mem]
  simpa only [Finset.sum_const, nsmul_eq_mul] using
    Finset.sum_le_sum (s := S) hlo

theorem event_finset_mem_pos {α : Type*} (μ : Mass α) (S : Finset α)
    (hS : S.Nonempty) {b : ℝ} (hb : 0 < b) (hlo : ∀ x ∈ S, b ≤ μ x) :
    0 < event μ (fun x => x ∈ S) := by
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  exact (mul_pos hc hb).trans_le (event_finset_mem_lower μ S hlo)

theorem conditionMass_finset_uniform_bound {α : Type*} (μ : Mass α) (S : Finset α)
    (hS : S.Nonempty) {b D : ℝ} (hb : 0 < b) (hD : 0 ≤ D)
    (hlo : ∀ x ∈ S, b ≤ μ x) (hhi : ∀ x ∈ S, μ x ≤ D * b) (x : α) :
    conditionMass μ (fun y => y ∈ S) x ≤ D * uniformFinsetMass S x := by
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have he := event_finset_mem_lower μ S hlo
  have hepos := event_finset_mem_pos μ S hS hb hlo
  rw [conditionMass_apply, uniformFinsetMass, flatMass_apply]
  by_cases hx : x ∈ S
  · rw [if_pos hx, if_pos hx]
    apply (div_le_iff₀ hepos).mpr
    calc
      μ x ≤ D * b := hhi x hx
      _ = (D * (S.card : ℝ)⁻¹) * ((S.card : ℝ) * b) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left he (mul_nonneg hD (inv_nonneg.mpr hc.le))
  · simp [hx]

theorem event_pointwise_domination {α : Type*} (μ ν : Mass α) {D : ℝ}
    (h : ∀ x, μ x ≤ D * ν x) (B : α → Prop) : event μ B ≤ D * event ν B := by
  rw [event_eq_sum μ B (Finset.subset_union_left (s₂ := ν.support)),
    event_eq_sum ν B (Finset.subset_union_right (s₁ := μ.support)), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : B x <;> simp only [hx, if_true, if_false, mul_zero]
  · exact h x
  · exact le_rfl

end Hindman168.FiniteMass
