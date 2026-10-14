import Hindman168.NativePieceRecipes

/-! Restrict an actual representing family to any chosen set of stages,
putting zero outside it without changing native geometry or bounds. -/
namespace Hindman168
open NNReal
open scoped Classical
universe u

theorem nativePieceOn_stage_restrict {s N : ℕ} (D : NativeNilmanifoldData.{u} s)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (f : ℕ → ℤ → ℝ)
    (hf : nativePieceOn D F gap f) (A : Set ℕ) :
    nativePieceOn D F gap (fun w y => if w ∈ A then f w y else 0) := by
  classical
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨obs, g, x, B, Lip, hB, hb, hl, rfl⟩ := hf
  refine ⟨fun w p => if w ∈ A then obs w p else ContinuousMap.const _ 0,
    g, x, B, Lip, hB, ?_, ?_, ?_⟩
  · intro w p z
    dsimp only
    split_ifs with hw
    · exact hb w p z
    · simpa using hB
  · intro w p
    dsimp only
    split_ifs with hw
    · exact hl w p
    · exact (LipschitzWith.const (0 : ℝ)).weaken (show 0 ≤ Lip from zero_le)
  · funext w y
    unfold piecewiseLinearNilsequence
    dsimp only
    split_ifs <;> rfl

theorem nativePieceRepresented_stage_restrict {s N : ℕ}
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (f : ℕ → ℤ → ℝ)
    (hf : NativePieceRepresented.{u} s F gap f) (A : Set ℕ) :
    NativePieceRepresented.{u} s F gap (fun w y => if w ∈ A then f w y else 0) := by
  obtain ⟨D, hD⟩ := hf
  exact ⟨D, nativePieceOn_stage_restrict D F gap f hD A⟩

end Hindman168

