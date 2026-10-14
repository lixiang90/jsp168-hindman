import Hindman168.MaskColorFamilyChainReplacement
import Hindman168.MaskFiniteModelReplacementFamily
import Hindman168.MasterGapIndex
import Hindman168.SelectedChainIndices

/-! Actual selected principal coordinates supply every hypothesis needed
for the preselected color dense family at the common first fine padding. -/

namespace Hindman168
open Filter
open scoped Topology Classical

theorem mask_color_family_selected_chain_quality (ι : Type*) [Fintype ι]
    {r M n : ℕ} (m d₀ : ℕ) (hM : 0 < M)
    (a : ι → ℚ) (ha : ∀ γ, 0 < a γ) (χ : ℕ → Fin r) (color : ι → Fin r)
    (f : Finset ℕ → (i : ℕ) → ι →
      boundedHilbertFamilies (fun w => FiniteMassL2
        (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hM⟩)) i w)))
    (hf : ∀ T i γ w y, 0 ≤ (f T i γ).val w y ∧ (f T i γ).val w y ≤ 1)
    (hd : ∀ T : Finset ℕ, ∀ i : Fin M, ∀ hT : T.Nonempty,
      ∀ hTi : T ⊆ Finset.range i.val, ∀ γ : ι,
      MaskColorBlockDualControl m d₀ hM T i hT hTi (a γ) χ (color γ)
        (fun w y => (f T i.val γ).val w y))
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (C : Chain (m+1)) (hC : ∀ col, C.block col ⊆ energyPrincipalSet e)
    (p : Fin (m+1) → Fin n) (hp : ∀ col, energyPrincipal e (p col) = C.pivot col)
    (γ : Fin (m+1) → ι) :
    let hCrange : ∀ col, C.block col ⊆ Finset.range M := fun col y hy => by
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp (hC col hy)
      exact Finset.mem_range.mpr (heM _)
    let gap := masterGapIndex M hM (energyPadding e (p 0))
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop,
      maskModelReplacementQuality gap (fun col => a (γ col)) (fun _ => C)
        (maskChainColorWeight m hM C hCrange (fun col => a (γ col)) χ
          (fun col => color (γ col)))
        (fun col w y => (f (C.tail col) (C.pivot col) (γ col)).val w y) ε w := by
  intro hCrange gap ε hε
  let l := gap 0
  have hval : l.val = energyPadding e (p 0) := masterGapIndex_val M hM _ 0 (heM _)
  have hpad := selected_chain_common_padding e C hC p hp
  have hgap (col : Fin (m+1)) : l.val ≤ C.pivot col := by
    rw [hval]
    exact (hpad.2.2 col).1.trans (hpad.2.2 col).2.le
  have htail (col : Fin (m+1)) : C.tail col ⊆ Finset.range l.val := by
    rw [hval]
    intro y hy
    exact Finset.mem_range.mpr (hpad.2.1 col y hy)
  exact mask_color_family_chain_replacements ι m d₀ hM a ha χ color f hf hd C hCrange
    l hgap htail γ ε hε

end Hindman168
