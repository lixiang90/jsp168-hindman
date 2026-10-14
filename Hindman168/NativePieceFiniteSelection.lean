import Hindman168.NativeFiniteRecipeBounds

namespace Hindman168
open NNReal
open scoped Classical
universe u v

/-- Choose one of finitely many native recipes separately on each actual
piece, with a zero branch. The same manifold and finite uniform bounds
work across all stages and pieces. -/
theorem nativePieceOn_piece_select {s N : ℕ} (D : NativeNilmanifoldData.{u} s)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) {ι : Type v} [Fintype ι]
    (f : ι → ℕ → ℤ → ℝ) (hf : ∀ i, nativePieceOn D F gap (f i))
    (σ : ℕ → (ℤ × ℤ) → Option ι) :
    nativePieceOn D F gap (fun w y =>
      (σ w (intervalResiduePiece (F.gap w (gap w).val) (F.modulus w : ℕ) y)).elim
        0 (fun i => f i w y)) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨B, Lip, hB, hreps⟩ := nativePieceOn_finite_uniform_bounds D F gap f hf
  choose obs g x hb hl he using hreps
  refine ⟨fun w p => (σ w p).elim (ContinuousMap.const _ 0) (fun i => obs i w p),
    (fun w p => (σ w p).elim 1 (fun i => g i w p)),
    (fun w p => (σ w p).elim 1 (fun i => x i w p)), B, Lip, hB, ?_, ?_, ?_⟩
  · intro w p z
    cases hs : σ w p with
    | none => simpa only [hs, Option.elim_none, ContinuousMap.const_apply, abs_zero] using hB
    | some i => simpa only [hs, Option.elim_some] using hb i w p z
  · intro w p
    cases hs : σ w p with
    | none =>
        simp only [hs, Option.elim_none]
        change LipschitzWith Lip (fun _ : D.G ⧸ D.Γ => (0 : ℝ))
        exact (LipschitzWith.const (0 : ℝ)).weaken (show 0 ≤ Lip from zero_le)
    | some i => simpa only [hs, Option.elim_some] using hl i w p
  · funext w y
    cases hs : σ w (intervalResiduePiece (F.gap w (gap w).val) (F.modulus w : ℕ) y) with
    | none => simp only [hs, Option.elim_none, piecewiseLinearNilsequence,
        ContinuousMap.const_apply]
    | some i =>
        rw [Option.elim_some]
        rw [he i]
        simp only [piecewiseLinearNilsequence, hs, Option.elim_some, pieceLinearOrbit]

theorem nativePieceRepresented_piece_select {s N : ℕ}
    (F : MasterParameterFamily) (gap : ℕ → Fin N) {ι : Type v} [Fintype ι]
    (f : ι → ℕ → ℤ → ℝ) (hf : ∀ i, NativePieceRepresented.{u} s F gap (f i))
    (σ : ℕ → (ℤ × ℤ) → Option ι) :
    NativePieceRepresented.{u} s F gap (fun w y =>
      (σ w (intervalResiduePiece (F.gap w (gap w).val) (F.modulus w : ℕ) y)).elim
        0 (fun i => f i w y)) := by
  obtain ⟨D, hD⟩ := nativePieceRepresented_finite_common (trivialNativeNilmanifold s) F gap f hf
  exact ⟨D, nativePieceOn_piece_select D F gap f hD σ⟩

theorem piece_selected_family_unit {N : ℕ} (F : MasterParameterFamily)
    (gap : ℕ → Fin N) {ι : Type v} (f : ι → ℕ → ℤ → ℝ)
    (hf : ∀ i w y, |f i w y| ≤ 1) (σ : ℕ → (ℤ × ℤ) → Option ι) (w : ℕ) (y : ℤ) :
    |(σ w (intervalResiduePiece (F.gap w (gap w).val) (F.modulus w : ℕ) y)).elim
      0 (fun i => f i w y)| ≤ 1 := by
  cases hs : σ w (intervalResiduePiece (F.gap w (gap w).val) (F.modulus w : ℕ) y) with
  | none => simp only [Option.elim_none, abs_zero, zero_le_one]
  | some i => simpa only [hs, Option.elim_some] using hf i w y

end Hindman168
