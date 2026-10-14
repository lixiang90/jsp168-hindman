import Hindman168.FiniteEventMajorization
import Hindman168.HarmonicMass

/-! Uniform bounds for the original rough harmonic law on a real interval.
The comparison interval may extend beyond the original cutoff. Keeping
the unit density in both numerator and denominator avoids a loss in W. -/

namespace Hindman168

open FiniteMass
open scoped BigOperators Classical

theorem rawMass_interval_event_le {X W : ℕ} (hZ : 0 < harmonicNormalizer X W)
    (A B : ℝ) :
    event (rawMass X W) (fun p => A ≤ (p : ℝ) ∧ (p : ℝ) < B) ≤
      roughResidueHarmonic A B W 1 0 / harmonicNormalizer X W := by
  rw [← intervalMass_total A B W (harmonicNormalizer X W)]
  apply event_le_total_of_pointwise
  intro p
  by_cases he : A ≤ (p : ℝ) ∧ (p : ℝ) < B
  · rw [if_pos he, rawMass_apply, harmonicWeight]
    by_cases hp : p ∈ harmonicWindow X W
    · rw [if_pos hp, intervalMass_apply, if_pos (mem_unitInterval.mpr
        ⟨he.1, he.2, (Finset.mem_filter.mp hp).2⟩)]
    · rw [if_neg hp]
      exact intervalMass_nonneg A B W hZ p
  · rw [if_neg he]
    exact intervalMass_nonneg A B W hZ p

theorem roughHarmonic_interval_upper {A B : ℝ} {W : ℕ}
    (hA : 0 < A) (hAB : A < B) (hW : 0 < W) :
    roughResidueHarmonic A B W 1 0 ≤ unitDensity W * (Real.log (B / A) + W / A) := by
  have hh := (abs_le.mp (periodic_harmonic_error hA hAB hW
    (by decide : 0 < 1) (by simp : W.Coprime 1) (by decide : 0 < 1))).2
  simp only [Nat.cast_one, div_one] at hh
  have hWR : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  have he : unitDensity W * (Real.log (B / A) + W / A) =
      unitDensity W * Real.log (B / A) + (W.totient : ℝ) / A := by
    unfold unitDensity
    field_simp
  rw [he]
  linarith

theorem rawMass_interval_log_bound {X W : ℕ} (hX : 2 ≤ X) (hW : 0 < W)
    (hlog : (W : ℝ) / X < Real.log X) {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    event (rawMass X W) (fun p => A ≤ (p : ℝ) ∧ (p : ℝ) < B) ≤
      (Real.log (B / A) + W / A) / (Real.log X - W / X) := by
  have hZ := harmonicNormalizer_pos hX hW hlog
  have hd := unitDensity_pos hW
  have hl : 0 < Real.log (B / A) := Real.log_pos ((lt_div_iff₀ hA).mpr (by simpa using hAB))
  have hn : 0 ≤ unitDensity W * (Real.log (B / A) + W / A) := by positivity
  calc
    _ ≤ roughResidueHarmonic A B W 1 0 / harmonicNormalizer X W := rawMass_interval_event_le hZ A B
    _ ≤ (unitDensity W * (Real.log (B / A) + W / A)) / harmonicNormalizer X W :=
      div_le_div_of_nonneg_right (roughHarmonic_interval_upper hA hAB hW) hZ.le
    _ ≤ (unitDensity W * (Real.log (B / A) + W / A)) /
        (unitDensity W * (Real.log X - W / X)) :=
      div_le_div_of_nonneg_left hn (mul_pos hd (sub_pos.mpr hlog)) (harmonicNormalizer_lower hX hW)
    _ = _ := by rw [mul_div_mul_left _ _ hd.ne']

end Hindman168
