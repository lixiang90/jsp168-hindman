import Hindman168.MaskColorFamilyChainReplacement
import Hindman168.MaskFiniteModelReplacementFamily

/-! Every permissible gap at a tracked block gives the original chain
dual control for the same coloring dense model. Only the tracked tail and
pivot are ordered here, so this applies at its own coarse padding as well
as at the common fine padding used by the subset correlation estimate. -/

namespace Hindman168
open Filter
open scoped Topology Classical

theorem maskColorBlockDualControl_chain {r N : ℕ} (m d₀ : ℕ) (hN : 0 < N)
    (C : Chain (m+1)) (hC : ∀ col, C.block col ⊆ Finset.range N)
    (a : Fin (m+1) → ℚ) (χ : ℕ → Fin r) (color : Fin (m+1) → Fin r)
    (col : Fin (m+1)) (l : Fin N)
    (htail : C.tail col ⊆ Finset.range l.val) (hgap : l.val ≤ C.pivot col)
    (model : ℕ → ℤ → ℝ)
    (hd : MaskColorBlockDualControl m d₀ hN (C.tail col)
      ⟨C.pivot col, Finset.mem_range.mp (hC col (by simp [Chain.block]))⟩ (C.tail_nonempty col)
      (fun _ hx => Finset.mem_range.mpr (C.tails_before_pivots col col _ hx))
      (a col) χ (color col) model) :
    maskBlockModelDualControl (fun _ => l) (fun _ => C) d₀
      (maskChainColorWeight m hN C hC a χ color col) model col := by
  let i : Fin N := ⟨C.pivot col, Finset.mem_range.mp (hC col (by simp [Chain.block]))⟩
  let gap : MaskValidBlockGap (C.tail col) i := ⟨l, htail, hgap⟩
  intro t J hJ η hη
  have h := hd gap t J (Nat.succ_le_iff.mpr hJ) η hη
  filter_upwards [h] with w hw
  intro u hu
  exact hw u hu

theorem mask_color_family_coarse_dual_control (ι : Type*) [Fintype ι]
    {r N : ℕ} (m d₀ : ℕ) (hN : 0 < N)
    (a : ι → ℚ) (χ : ℕ → Fin r) (color : ι → Fin r)
    (f : Finset ℕ → (i : ℕ) → ι →
      boundedHilbertFamilies (fun w => FiniteMassL2
        (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) i w)))
    (hd : ∀ T : Finset ℕ, ∀ i : Fin N, ∀ hT : T.Nonempty,
      ∀ hTi : T ⊆ Finset.range i.val, ∀ γ : ι,
      MaskColorBlockDualControl m d₀ hN T i hT hTi (a γ) χ (color γ)
        (fun w y => (f T i.val γ).val w y))
    (C : Chain (m+1)) (hC : ∀ col, C.block col ⊆ Finset.range N)
    (γ : Fin (m+1) → ι) (col : Fin (m+1)) (l : Fin N)
    (htail : C.tail col ⊆ Finset.range l.val) (hgap : l.val ≤ C.pivot col) :
    maskBlockModelDualControl (fun _ => l) (fun _ => C) d₀
      (maskChainColorWeight m hN C hC (fun col => a (γ col)) χ (fun col => color (γ col)) col)
      (fun w y => (f (C.tail col) (C.pivot col) (γ col)).val w y) col := by
  exact maskColorBlockDualControl_chain m d₀ hN C hC (fun col => a (γ col)) χ
    (fun col => color (γ col)) col l htail hgap _ (hd _ _ _ _ _)

end Hindman168
