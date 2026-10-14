import Hindman168.FiniteExposureEventDisintegration
import Hindman168.FiniteSupportedEventComparison
import Hindman168.FiniteEventMajorization

/-! Uniform actual conditional caps on good exposed keys integrate to the
ORIGINAL finite mass. Bad keys are charged their original mass; neither
independence nor positive conditional likelihood is assumed on bad keys. -/
namespace Hindman168
open FiniteMass
open scoped BigOperators Classical

theorem finite_good_exposure_event_bound {α β : Type*} (μ : Mass α) (f : α → β)
    (Good : β → Prop) (B : α → Prop) (hμ : ∀ x, 0 ≤ μ x) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcap : ∀ x ∈ μ.support, Good (f x) →
      event (conditionMass μ (fun y => f y=f x)) B ≤ δ) :
    event μ (fun x => Good (f x) ∧ B x) ≤ δ*total μ := by
  rw [←finite_exposure_event_disintegration μ f _ hμ]
  rw [expectation_eq_sum _ _ (Finset.Subset.refl _)]
  have htotal : (∑ key ∈ (μ.mapDomain f).support, (μ.mapDomain f) key*δ)=δ*total μ := by
    rw [←Finset.sum_mul,←total_eq_sum _ (Finset.Subset.refl _),total_push,mul_comm]
  rw [←htotal]
  apply Finset.sum_le_sum
  intro key hk
  obtain ⟨x,hx,hfx⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hk)
  apply mul_le_mul_of_nonneg_left _ (push_nonneg μ f hμ key)
  by_cases hg : Good key
  · have hc := hcap x hx (hfx.symm ▸ hg)
    rw [hfx] at hc
    exact (event_mono (conditionMass μ (fun y => f y=key)) (conditionMass_nonneg _ _ hμ)
      (fun _ h => h.2)).trans hc
  · have hz : event (conditionMass μ (fun y => f y=key)) (fun y => Good (f y) ∧ B y)=0 := by
      rw [←event_false (conditionMass μ (fun y => f y=key))]
      apply event_congr_on_support
      intro y hy
      have hf : f y=key := by
        by_contra hn
        have hnz := Finsupp.mem_support_iff.mp hy
        rw [conditionMass_apply,if_neg hn] at hnz
        exact hnz rfl
      simp only [hf,hg,false_and]
    rw [hz]
    exact hδ

theorem finite_typical_exposure_event_bound {α β : Type*} (μ : Mass α) (f : α → β)
    (Good : β → Prop) (B : α → Prop) (hμ : ∀ x, 0 ≤ μ x) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcap : ∀ x ∈ μ.support, Good (f x) →
      event (conditionMass μ (fun y => f y=f x)) B ≤ δ) :
    event μ B ≤ δ*total μ+event μ (fun x => ¬ Good (f x)) := by
  have hm := event_mono μ hμ (E := B)
    (F := fun x => (Good (f x) ∧ B x) ∨ ¬ Good (f x)) (fun x hb => by
      by_cases hg : Good (f x)
      · exact Or.inl ⟨hg,hb⟩
      · exact Or.inr hg)
  have hu := event_or_le_add μ (fun x => Good (f x) ∧ B x) (fun x => ¬ Good (f x)) hμ
  have hc := finite_good_exposure_event_bound μ f Good B hμ hδ hcap
  linarith

end Hindman168
