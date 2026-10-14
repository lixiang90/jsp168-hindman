import Hindman168.BoundedHilbertFamilies

/-! Compact bounds along the actual ultrafilter prove convergence of
the original sequence; no global modification of early terms is used. -/

namespace Hindman168
open Filter
open scoped Topology

theorem eventual_Icc_ultrafilter_tendsto (U : Ultrafilter ℕ) (f : ℕ → ℝ)
    (a b : ℝ) (hf : ∀ᶠ w in (U : Filter ℕ), f w ∈ Set.Icc a b) :
    Tendsto f (U : Filter ℕ) (𝓝 (limUnder (U : Filter ℕ) f)) := by
  have hm : (Ultrafilter.map f U : Filter ℝ) ≤ 𝓟 (Set.Icc a b) := by
    rw [Ultrafilter.coe_map, Filter.le_principal_iff]
    exact hf
  obtain ⟨x, _, hx⟩ := isCompact_Icc.ultrafilter_le_nhds (Ultrafilter.map f U) hm
  exact tendsto_nhds_limUnder ⟨x, hx⟩

theorem eventual_Icc_ultrafilter_limit (U : Ultrafilter ℕ) (f : ℕ → ℝ)
    (a b : ℝ) (hf : ∀ᶠ w in (U : Filter ℕ), f w ∈ Set.Icc a b) :
    Tendsto f (U : Filter ℕ) (𝓝 (limUnder (U : Filter ℕ) f)) ∧
      limUnder (U : Filter ℕ) f ∈ Set.Icc a b := by
  have ht := eventual_Icc_ultrafilter_tendsto U f a b hf
  exact ⟨ht, ge_of_tendsto ht (hf.mono (fun _ h => h.1)),
    le_of_tendsto ht (hf.mono (fun _ h => h.2))⟩

theorem eventual_abs_error_ultrafilter_limit (U : Ultrafilter ℕ) (f : ℕ → ℝ)
    (B : ℝ) (hf : ∀ᶠ w in (U : Filter ℕ), |f w| < B) :
    Tendsto (fun w => |f w|) (U : Filter ℕ)
      (𝓝 (limUnder (U : Filter ℕ) (fun w => |f w|))) ∧
      limUnder (U : Filter ℕ) (fun w => |f w|) ∈ Set.Icc 0 B :=
  eventual_Icc_ultrafilter_limit U _ 0 B (hf.mono (fun _ hw => ⟨abs_nonneg _, hw.le⟩))

end Hindman168
