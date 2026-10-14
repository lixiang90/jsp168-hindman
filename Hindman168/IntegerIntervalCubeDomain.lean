import Hindman168.IntegerCubeCornerCoordinates
import Mathlib.Data.Int.Interval

namespace Hindman168
open scoped BigOperators Classical

/-- The finite integer cube domain whose every vertex lies in [0,L).
The bounding box imposes no additional restriction on such a cube. -/
noncomputable def integerIntervalCubeDomain (d L : ℕ) : Finset (ℤ × (Fin d → ℤ)) :=
  ((Finset.Ico 0 (L : ℤ)).product
    (Fintype.piFinset (fun _ : Fin d => Finset.Ico (-(L : ℤ)) L))).filter
      (fun p => ∀ ω : Finset (Fin d), 0 ≤ integerCubeVertex p ω ∧ integerCubeVertex p ω < L)

theorem mem_integerIntervalCubeDomain {d L : ℕ} (p : ℤ × (Fin d → ℤ)) :
    p ∈ integerIntervalCubeDomain d L ↔
      ∀ ω : Finset (Fin d), 0 ≤ integerCubeVertex p ω ∧ integerCubeVertex p ω < L := by
  constructor
  · intro hp
    exact (Finset.mem_filter.mp hp).2
  · intro hp
    have hr : 0 ≤ p.1 ∧ p.1 < L := by
      simpa only [integerCubeVertex, Finset.sum_empty, add_zero] using hp ∅
    have hv (j : Fin d) : -(L : ℤ) ≤ p.2 j ∧ p.2 j < L := by
      have hn : 0 ≤ p.1 + p.2 j ∧ p.1 + p.2 j < L := by
        simpa only [integerCubeVertex, Finset.sum_singleton] using hp {j}
      omega
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr hr,
      Fintype.mem_piFinset.mpr (fun j => Finset.mem_Ico.mpr (hv j))⟩, hp⟩

theorem integerIntervalCubeDomain_nonempty (d L : ℕ) (hL : 0 < L) :
    (integerIntervalCubeDomain d L).Nonempty := by
  refine ⟨(0, fun _ => 0), (mem_integerIntervalCubeDomain _).mpr ?_⟩
  intro ω
  simp only [integerCubeVertex, Finset.sum_const_zero, add_zero]
  exact ⟨le_rfl, by exact_mod_cast hL⟩

end Hindman168
