import Hindman168.PrincipalPredictionLimits

/-! The precise fixed-ultrafilter output uses the same selected laws,
weighted count, bounded models and complete product-color masks. -/

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

structure PrincipalPredictionLimitData {n m r : ℕ} {ι : Type*}
    (M : ℕ) (e : Fin (2*n) ↪o ℕ) (F : MasterParameterFamily)
    (U : Ultrafilter ℕ) (cap η : ℝ) (a : ι → ℚ) (χ : ℕ → Fin r) (color : ι → Fin r)
    (S : Finset (Fin n) → Fin n → ι → ℕ → ℤ → ℝ) : Prop where
  calibration : ∀ (T : Finset (Fin n)) (b : Fin n) (γ : ι),
    T.Nonempty → (∀ k ∈ T, k < b) → ∀ θ : ℝ, 0 < θ →
      Tendsto (principalCalibrationProbability M e F T b (a γ) χ (color γ) (S T b γ) θ)
        (U : Filter ℕ) (𝓝 (limUnder (U : Filter ℕ)
          (principalCalibrationProbability M e F T b (a γ) χ (color γ) (S T b γ) θ))) ∧
      0 ≤ limUnder (U : Filter ℕ)
        (principalCalibrationProbability M e F T b (a γ) χ (color γ) (S T b γ) θ) ∧
      limUnder (U : Filter ℕ)
        (principalCalibrationProbability M e F T b (a γ) χ (color γ) (S T b γ) θ) ≤ 3*θ + cap
  model_counts : ∀ (C : PrincipalCoordinateChain n (m+1))
    (γ : Fin (m+1) → ι) (productColor : Fin r),
    let B := principalModelColorCount C M e F (fun col => a (γ col)) χ productColor
      (fun col => S (C.tail col) (C.pivot col) (γ col))
    Tendsto B (U : Filter ℕ) (𝓝 (limUnder (U : Filter ℕ) B)) ∧
      limUnder (U : Filter ℕ) B ∈ Set.Icc (0 : ℝ) 1
  weighted_counts : ∀ (C : PrincipalCoordinateChain n (m+1))
    (γ : Fin (m+1) → ι) (productColor : Fin r),
    let I := principalWeightedColorCount C M e F (fun col => a (γ col)) χ
      (fun col => color (γ col)) productColor
    let B := principalModelColorCount C M e F (fun col => a (γ col)) χ productColor
      (fun col => S (C.tail col) (C.pivot col) (γ col))
    Tendsto B (U : Filter ℕ) (𝓝 (limUnder (U : Filter ℕ) B)) ∧
    Tendsto I (U : Filter ℕ) (𝓝 (limUnder (U : Filter ℕ) I)) ∧
    Tendsto (fun w => |I w - B w|) (U : Filter ℕ)
      (𝓝 (limUnder (U : Filter ℕ) (fun w => |I w - B w|))) ∧
    limUnder (U : Filter ℕ) (fun w => |I w - B w|) ∈ Set.Icc (0 : ℝ) η ∧
    |limUnder (U : Filter ℕ) I - limUnder (U : Filter ℕ) B| ≤ η

theorem principal_prediction_limit_data {n m r : ℕ} {ι : Type*}
    (M : ℕ) (e : Fin (2*n) ↪o ℕ) (F : MasterParameterFamily)
    (hprob : ∀ᶠ w in atTop, (∀ x, 0 ≤ selectedPrincipalRawMass e F w x) ∧
      total (selectedPrincipalRawMass e F w) = 1)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (cap η : ℝ) (a : ι → ℚ) (χ : ℕ → Fin r) (color : ι → Fin r)
    (S : Finset (Fin n) → Fin n → ι → ℕ → ℤ → ℝ)
    (hS : ∀ T b γ w y, S T b γ w y ∈ Set.Icc (0 : ℝ) 1)
    (hcal : ∀ (T : Finset (Fin n)) (b : Fin n) (γ : ι),
      T.Nonempty → (∀ k ∈ T, k < b) → ∀ θ : ℝ, 0 < θ → ∀ᶠ w in (U : Filter ℕ),
      principalCalibrationProbability M e F T b (a γ) χ (color γ) (S T b γ) θ w < 3*θ + cap)
    (hcount : ∀ (C : PrincipalCoordinateChain n (m+1))
      (γ : Fin (m+1) → ι) (productColor : Fin r), ∀ᶠ w in (U : Filter ℕ),
      |principalWeightedColorCount C M e F (fun col => a (γ col)) χ
          (fun col => color (γ col)) productColor w -
        principalModelColorCount C M e F (fun col => a (γ col)) χ productColor
          (fun col => S (C.tail col) (C.pivot col) (γ col)) w| < η) :
    PrincipalPredictionLimitData (m := m) M e F U cap η a χ color S := by
  refine ⟨?_, ?_, ?_⟩
  · intro T b γ hT hbefore θ hθ
    exact principal_calibration_ultrafilter_limit M e F hprob U hU T b (a γ) χ (color γ)
      (S T b γ) θ cap (hcal T b γ hT hbefore θ hθ)
  · intro C γ productColor
    exact principal_model_count_ultrafilter_limit (M := M) C e F hprob U hU (fun col => a (γ col)) χ
      productColor (fun col => S (C.tail col) (C.pivot col) (γ col))
      (fun col w y => hS _ _ _ w y)
  · intro C γ productColor
    exact principal_weighted_count_ultrafilter_limits (M := M) C e F hprob U hU (fun col => a (γ col)) χ
      (fun col => color (γ col)) productColor (fun col => S (C.tail col) (C.pivot col) (γ col))
      (fun col w y => hS _ _ _ w y) η (hcount C γ productColor)

end Hindman168
