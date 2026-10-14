import Hindman168.MaskBlockColorDenseModels
import Hindman168.OriginalMasterSelectedModels

/-! The actual all-gap color models form one family in the original pivot
Hilbert spaces before energy selection. Invalid block coordinates are assigned
zero; every valid block retains all row and zero-prime dual estimates. -/

namespace Hindman168
open Filter FiniteMass
open scoped Topology Classical

noncomputable def MaskColorBlockDualControl {r N : ℕ} (m d₀ : ℕ) (hN : 0 < N)
    (T : Finset ℕ) (i : Fin N) (hT : T.Nonempty) (hTi : T ⊆ Finset.range i.val)
    (a : ℚ) (χ : ℕ → Fin r) (c : Fin r) (model : ℕ → ℤ → ℝ) : Prop :=
  ∀ l : MaskValidBlockGap T i,
    ∀ t : Fin (Fintype.card (LargeColumnSubset m) + 1),
    ∀ J : ℕ, 1 ≤ J → ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
    ∀ u : OriginalSingleDualInput
      (maskGeneratedDualTemplates m (fun _ => l.val) d₀ (fun _ => l.val) t).arity
      (maskGeneratedDualTemplates m (fun _ => l.val) d₀ (fun _ => l.val) t).dimension,
    u.Admissible (maskGeneratedMaster m (fun _ => ⟨0, hN⟩))
      (fun _ => maskBlockChain T i.val hT hTi) (fun _ => 0) w →
    |expectation (integerMass ((maskGeneratedMaster m (fun _ => ⟨0, hN⟩)).cutoff w i.val)
      (primorial w)) (fun y => (maskBlockColorWeight m hN T i hT hTi a χ c w y - model w y) *
        (maskGeneratedDualTemplates m (fun _ => l.val) d₀ (fun _ => l.val) t).dual
          (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) (fun _ => J) u w y)| < η

theorem mask_color_block_hilbert_family (ι : Type*) [Fintype ι]
    {r N : ℕ} (m d₀ : ℕ) (hd₀ : 0 < d₀) (hN : 0 < N)
    (a : ι → ℚ) (ha : ∀ γ, 0 < a γ) (χ : ℕ → Fin r) (color : ι → Fin r) :
    ∃ f : Finset ℕ → (i : ℕ) → ι →
      boundedHilbertFamilies (fun w => FiniteMassL2
        (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) i w)),
      (∀ T i γ w y, 0 ≤ (f T i γ).val w y ∧ (f T i γ).val w y ≤ 1) ∧
      ∀ T : Finset ℕ, ∀ i : Fin N, ∀ hT : T.Nonempty,
        ∀ hTi : T ⊆ Finset.range i.val, ∀ γ : ι,
        MaskColorBlockDualControl m d₀ hN T i hT hTi (a γ) χ (color γ)
          (fun w y => (f T i.val γ).val w y) := by
  have hraw (T : Finset ℕ) (i : ℕ) (γ : ι) :
      ∃ g : ℕ → ℤ → ℝ, (∀ w y, 0 ≤ g w y ∧ g w y ≤ 1) ∧
        ∀ hi : i < N, ∀ hT : T.Nonempty, ∀ hTi : T ⊆ Finset.range i,
          MaskColorBlockDualControl m d₀ hN T ⟨i, hi⟩ hT hTi (a γ) χ (color γ) g := by
    by_cases h : i < N ∧ T.Nonempty ∧ T ⊆ Finset.range i
    · obtain ⟨g, hg, hd⟩ := maskBlock_coloring_all_gap_dense_models m d₀ hd₀ hN T
        ⟨i, h.1⟩ h.2.1 h.2.2 (a γ) (ha γ) χ (color γ)
      exact ⟨g, hg, fun _ _ _ => hd⟩
    · refine ⟨fun _ _ => 0, fun _ _ => by norm_num, ?_⟩
      intro hi hT hTi
      exact False.elim (h ⟨hi, hT, hTi⟩)
  choose g hg hd using hraw
  let F := maskGeneratedMaster m (fun _ => (⟨0, hN⟩ : Fin N))
  let f (T : Finset ℕ) (i : ℕ) (γ : ι) :=
    masterOriginalBoundedFamily F (fun _ => i) (g T i γ) 1 zero_le_one
      (fun w y => by rw [abs_of_nonneg (hg T i γ w y).1]; exact (hg T i γ w y).2)
  refine ⟨f, ?_, ?_⟩
  · exact hg
  · intro T i hT hTi γ
    exact hd T i.val γ i.isLt hT hTi

end Hindman168
