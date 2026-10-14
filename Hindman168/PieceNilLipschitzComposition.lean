import Hindman168.BoundedPieceNilFamilies
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Actual observable composition and unit-interval clipping preserve
the same quotient and globally bounded piecewise representation. -/

namespace Hindman168
open NNReal

def unitIntervalClip (t : ℝ) : ℝ := max 0 (min 1 t)

theorem unitIntervalClip_bounds (t : ℝ) : 0 ≤ unitIntervalClip t ∧ unitIntervalClip t ≤ 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem unitIntervalClip_lipschitz : LipschitzWith 1 unitIntervalClip :=
  (LipschitzWith.id.const_min 1).const_max 0

theorem unitIntervalClip_distance_le (x t : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    |x - unitIntervalClip t| ≤ |x - t| := by
  have he : unitIntervalClip x = x := by simp [unitIntervalClip, hx.1, hx.2]
  simpa only [Real.dist_eq, he, NNReal.coe_one, one_mul] using
    unitIntervalClip_lipschitz.dist_le_mul x t

theorem boundedPieceNilsequence_lipschitz_comp {G : Type*} [Group G]
    (Γ : Subgroup G) [MetricSpace (G ⧸ Γ)] {N : ℕ}
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (f : ℕ → ℤ → ℝ)
    (hf : IsBoundedPieceNilsequence Γ F gap f) (ψ : ℝ → ℝ) (K : ℝ≥0)
    (hψ : LipschitzWith K ψ) : IsBoundedPieceNilsequence Γ F gap (fun w y => ψ (f w y)) := by
  obtain ⟨obs, g, x, B, Lip, hB, hb, hl, rfl⟩ := hf
  let ψc : C(ℝ, ℝ) := ⟨ψ, hψ.continuous⟩
  refine ⟨fun w p => ψc.comp (obs w p), g, x, (K : ℝ) * B + |ψ 0|, K * Lip,
    add_nonneg (mul_nonneg K.coe_nonneg hB) (abs_nonneg _), ?_, ?_, rfl⟩
  · intro w p z
    change |ψ (obs w p z)| ≤ _
    have hd := hψ.dist_le_mul (obs w p z) 0
    simp only [Real.dist_eq, sub_zero] at hd
    calc
      |ψ (obs w p z)| ≤ |ψ (obs w p z) - ψ 0| + |ψ 0| := by
        simpa only [sub_add_cancel] using abs_add_le (ψ (obs w p z) - ψ 0) (ψ 0)
      _ ≤ (K : ℝ) * B + |ψ 0| := add_le_add
        (hd.trans (mul_le_mul_of_nonneg_left (hb w p z) K.coe_nonneg)) le_rfl
  · exact fun w p => hψ.comp (hl w p)

theorem boundedPieceNilsequence_clip {G : Type*} [Group G]
    (Γ : Subgroup G) [MetricSpace (G ⧸ Γ)] {N : ℕ}
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (f : ℕ → ℤ → ℝ)
    (hf : IsBoundedPieceNilsequence Γ F gap f) :
    IsBoundedPieceNilsequence Γ F gap (fun w y => unitIntervalClip (f w y)) :=
  boundedPieceNilsequence_lipschitz_comp Γ F gap f hf unitIntervalClip 1 unitIntervalClip_lipschitz

end Hindman168
