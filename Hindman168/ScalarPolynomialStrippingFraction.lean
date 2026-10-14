import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

namespace Hindman168

theorem scalar_polynomial_stripping_fraction (d : ℕ) (B δ : ℝ)
    (hB : 1 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 4*B*ρ ≤ δ ∧
      2*Real.pi*(d+1 : ℕ)*B*ρ ≤ δ/8 := by
  let ρ := min (δ/(8*B)) (δ/(32*Real.pi*(d+1 : ℕ)*B))
  have hBpos : 0 < B := by linarith
  have hDpos : 0 < 32*Real.pi*(d+1 : ℕ)*B := by positivity
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρ8 : ρ ≤ δ/(8*B) := min_le_left _ _
  have hρ32 : ρ ≤ δ/(32*Real.pi*(d+1 : ℕ)*B) := min_le_right _ _
  have hwidth := (le_div_iff₀ (by positivity : 0 < 8*B)).mp hρ8
  have hphase := (le_div_iff₀ hDpos).mp hρ32
  refine ⟨ρ, hρ, ?_, ?_, ?_⟩
  · exact hρ8.trans ((div_le_one (by positivity)).mpr (by linarith))
  · nlinarith
  · nlinarith only [hphase, hδ]

end Hindman168

