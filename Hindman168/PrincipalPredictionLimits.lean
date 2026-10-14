import Hindman168.PrincipalModelCountBounds
import Hindman168.EventualUltrafilterBounds

/-! Calibration and count comparisons converge on the very same fixed
ultrafilter. Actual compact bounds prove existence of all stated limits. -/

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

theorem principal_calibration_ultrafilter_limit {n r : ℕ} (M : ℕ)
    (e : Fin (2*n) ↪o ℕ) (F : MasterParameterFamily)
    (hprob : ∀ᶠ w in atTop, (∀ x, 0 ≤ selectedPrincipalRawMass e F w x) ∧
      total (selectedPrincipalRawMass e F w) = 1)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (T : Finset (Fin n)) (b : Fin n) (a : ℚ) (χ : ℕ → Fin r) (color : Fin r)
    (S : ℕ → ℤ → ℝ) (θ cap : ℝ)
    (hcal : ∀ᶠ w in (U : Filter ℕ),
      principalCalibrationProbability M e F T b a χ color S θ w < 3*θ + cap) :
    Tendsto (principalCalibrationProbability M e F T b a χ color S θ) (U : Filter ℕ)
      (𝓝 (limUnder (U : Filter ℕ) (principalCalibrationProbability M e F T b a χ color S θ))) ∧
    0 ≤ limUnder (U : Filter ℕ) (principalCalibrationProbability M e F T b a χ color S θ) ∧
    limUnder (U : Filter ℕ) (principalCalibrationProbability M e F T b a χ color S θ) ≤ 3*θ + cap := by
  have hp := (principalCalibrationProbability_Icc M e F hprob T b a χ color S θ).filter_mono hU
  have ht := eventual_Icc_ultrafilter_tendsto U _ 0 1 hp
  exact ⟨ht, ge_of_tendsto ht (hp.mono (fun _ h => h.1)),
    le_of_tendsto ht (hcal.mono (fun _ h => h.le))⟩

theorem principal_model_count_ultrafilter_limit {n m M r : ℕ}
    (C : PrincipalCoordinateChain n (m+1)) (e : Fin (2*n) ↪o ℕ)
    (F : MasterParameterFamily)
    (hprob : ∀ᶠ w in atTop, (∀ x, 0 ≤ selectedPrincipalRawMass e F w x) ∧
      total (selectedPrincipalRawMass e F w) = 1)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (a : Fin (m+1) → ℚ) (χ : ℕ → Fin r) (color : Fin r)
    (S : Fin (m+1) → ℕ → ℤ → ℝ) (hS : ∀ col w y, S col w y ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (principalModelColorCount C M e F a χ color S) (U : Filter ℕ)
      (𝓝 (limUnder (U : Filter ℕ) (principalModelColorCount C M e F a χ color S))) ∧
    limUnder (U : Filter ℕ) (principalModelColorCount C M e F a χ color S) ∈ Set.Icc (0 : ℝ) 1 :=
  eventual_Icc_ultrafilter_limit U _ 0 1
    ((principalModelColorCount_Icc (M := M) C e F hprob a χ color S hS).filter_mono hU)

theorem principal_weighted_count_ultrafilter_limits {n m M r : ℕ}
    (C : PrincipalCoordinateChain n (m+1)) (e : Fin (2*n) ↪o ℕ)
    (F : MasterParameterFamily)
    (hprob : ∀ᶠ w in atTop, (∀ x, 0 ≤ selectedPrincipalRawMass e F w x) ∧
      total (selectedPrincipalRawMass e F w) = 1)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (a : Fin (m+1) → ℚ) (χ : ℕ → Fin r) (color : Fin (m+1) → Fin r) (productColor : Fin r)
    (S : Fin (m+1) → ℕ → ℤ → ℝ) (hS : ∀ col w y, S col w y ∈ Set.Icc (0 : ℝ) 1)
    (η : ℝ)
    (hcount : ∀ᶠ w in (U : Filter ℕ),
      |principalWeightedColorCount C M e F a χ color productColor w -
        principalModelColorCount C M e F a χ productColor S w| < η) :
    let I := principalWeightedColorCount C M e F a χ color productColor
    let B := principalModelColorCount C M e F a χ productColor S
    Tendsto B (U : Filter ℕ) (𝓝 (limUnder (U : Filter ℕ) B)) ∧
    Tendsto I (U : Filter ℕ) (𝓝 (limUnder (U : Filter ℕ) I)) ∧
    Tendsto (fun w => |I w - B w|) (U : Filter ℕ)
      (𝓝 (limUnder (U : Filter ℕ) (fun w => |I w - B w|))) ∧
    limUnder (U : Filter ℕ) (fun w => |I w - B w|) ∈ Set.Icc (0 : ℝ) η ∧
    |limUnder (U : Filter ℕ) I - limUnder (U : Filter ℕ) B| ≤ η := by
  intro I B
  have hb : Tendsto B (U : Filter ℕ) (𝓝 (limUnder (U : Filter ℕ) B)) ∧
      limUnder (U : Filter ℕ) B ∈ Set.Icc (0 : ℝ) 1 :=
    principal_model_count_ultrafilter_limit (M := M) C e F hprob U hU a χ productColor S hS
  have hd : ∀ᶠ w in (U : Filter ℕ), I w - B w ∈ Set.Icc (-η) η :=
    hcount.mono (fun _ h => ⟨(abs_lt.mp h).1.le, (abs_lt.mp h).2.le⟩)
  have htd := eventual_Icc_ultrafilter_tendsto U (fun w => I w - B w) (-η) η hd
  have hti' := htd.add hb.1
  have hti : Tendsto I (U : Filter ℕ) (𝓝 (limUnder (U : Filter ℕ) I)) :=
    tendsto_nhds_limUnder ⟨_, by simpa only [Pi.add_apply, sub_add_cancel] using hti'⟩
  have he := eventual_abs_error_ultrafilter_limit U (fun w => I w - B w) η hcount
  have hid := tendsto_nhds_unique he.1 ((hti.sub hb.1).abs)
  exact ⟨hb.1, hti, he.1, he.2, hid ▸ he.2.2⟩

end Hindman168
