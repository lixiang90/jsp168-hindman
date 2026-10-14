import Hindman168.NativeStageRestriction

namespace Hindman168
open NNReal
open scoped Classical
universe u

/-- Put zero on arbitrary stage-and-piece labels, retaining the original
native manifold, orbit data and uniform observable bounds. -/
theorem nativePieceOn_piece_restrict {s N : ℕ} (D : NativeNilmanifoldData.{u} s)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (f : ℕ → ℤ → ℝ)
    (hf : nativePieceOn D F gap f) (P : ℕ → (ℤ × ℤ) → Prop) :
    nativePieceOn D F gap (fun w y =>
      if P w (intervalResiduePiece (F.gap w (gap w).val) (F.modulus w : ℕ) y)
        then f w y else 0) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨obs, g, x, B, Lip, hB, hb, hl, rfl⟩ := hf
  refine ⟨fun w p => if P w p then obs w p else ContinuousMap.const _ 0,
    g, x, B, Lip, hB, ?_, ?_, ?_⟩
  · intro w p z
    dsimp only
    split_ifs with hp
    · exact hb w p z
    · simpa using hB
  · intro w p
    dsimp only
    split_ifs with hp
    · exact hl w p
    · exact (LipschitzWith.const (0 : ℝ)).weaken (show 0 ≤ Lip from zero_le)
  · funext w y
    unfold piecewiseLinearNilsequence
    dsimp only
    split_ifs <;> rfl

end Hindman168
