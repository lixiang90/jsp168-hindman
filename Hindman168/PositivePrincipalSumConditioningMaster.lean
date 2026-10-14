import Hindman168.PositivePrincipalSumConditioningOutside
import Hindman168.PositivePrincipalSumPivotMasterExtension

namespace Hindman168
open Filter FiniteMass
open scoped Topology BigOperators Classical

/-- The full original-harmonic §8.5 bridge. Local exact exposed laws and
vanishing fine-conditioning mass produce a uniform extension bound for
all earlier events; outside-good sets and translation errors are derived. -/
theorem principal_master_exposed_pivot_extension
    {d N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F)
    (i : Fin N) {α γ V : Type*} [Fintype V] [Nonempty V]
    (μ : ℕ → Mass α) (expose : ℕ → α → ℤ → γ)
    (good : ℕ → α → γ → Prop) (P : ℕ → α → ℤ → Prop)
    (s : V → ℕ → α → ℤ) (C : ℝ) (p Q : ℕ) (hC : 0 ≤ C) (hQ : 0 < Q)
    (hμ : ∀ᶠ w in atTop, (∀ x, 0 ≤ μ w x) ∧ total (μ w) = 1)
    (hs : ∀ᶠ w in atTop, ∀ v x, x ∈ (μ w).support →
      (primorial w : ℤ) ∣ s v w x ∧ |(s v w x : ℝ)| ≤ C * (F.auxiliary w i.val : ℝ)^p)
    (hlocal : ∀ᶠ w in atTop, ∀ x ∈ (μ w).support,
      ∀ t ∈ ((integerMass (F.cutoff w i.val) (primorial w)).mapDomain (expose w x)).support,
      good w x t → 1 / (2 * (Q : ℝ)) ≤ ∑ v,
        event (conditionMass (integerMass (F.cutoff w i.val) (primorial w))
          (fun z => expose w x z = t)) (fun z => P w x (z + s v w x)))
    (hbad : Tendsto (fun w => event
      (conditionalJoint (μ w) (fun _ => integerMass (F.cutoff w i.val) (primorial w)))
      (fun xz => ¬ good w xz.1 (expose w xz.1 xz.2))) atTop (𝓝 0)) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∀ E : α → Prop,
      (1 / (3 * (Q : ℝ) * (Fintype.card V : ℝ))) * event (μ w) E - err w ≤
        event (conditionalJoint (μ w) (fun _ => integerMass (F.cutoff w i.val) (primorial w)))
          (fun xp => E xp.1 ∧ P w xp.1 xp.2) := by
  have hν : ∀ᶠ w in atTop, ∀ _x : α,
      (∀ z, 0 ≤ integerMass (F.cutoff w i.val) (primorial w) z) ∧
      total (integerMass (F.cutoff w i.val) (primorial w)) = 1 := by
    filter_upwards [hF.raw_cutoffs_valid] with w hw x
    have hz := (hw i.val (Finset.mem_range.mpr i.isLt)).2.2
    exact ⟨integerMass_nonneg hz, integerMass_total hz⟩
  obtain ⟨G, hG, hcover⟩ := principal_fine_conditioning_to_outside_cover μ
    (fun w _ => integerMass (F.cutoff w i.val) (primorial w)) expose good
    (fun v w x z => P w x (z + s v w x)) Q hQ (hμ.mono (fun _ h => h.1)) hν hlocal hbad
  have hc : 0 ≤ (1 : ℝ) / (3 * Q) := by positivity
  obtain ⟨err, he, hbound⟩ := principal_master_pivot_extension hF i μ G P s C
    (1 / (3 * (Q : ℝ))) p hC hc hμ hG hs hcover
  exact ⟨err, he, by simpa only [div_div] using hbound⟩
end Hindman168
