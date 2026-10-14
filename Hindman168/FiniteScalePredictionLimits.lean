import Hindman168.FiniteScaleColorIndices

/-! The abstract finite-family limit data specializes to the paper's
actual finite scale lists: each column uses its own block product,
and the same color is required for every sum row and product mask. -/

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

theorem finite_scale_calibration_limit {n m r : ℕ}
    (M : ℕ) (e : Fin (2*n) ↪o ℕ) (F : MasterParameterFamily) (U : Ultrafilter ℕ)
    (cap η : ℝ) (A : Finset ℚ) (χ : ℕ → Fin r)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (hdata : PrincipalPredictionLimitData (m := m) M e F U cap η
      (scaleColorFactor A r) χ (scaleColorValue A r) S)
    (T : Finset (Fin n)) (pivot : Fin n) (hT : T.Nonempty)
    (hbefore : ∀ k ∈ T, k < pivot) (a : ℚ) (ha : a ∈ A) (color : Fin r)
    (θ : ℝ) (hθ : 0 < θ) :
    let f := principalCalibrationProbability M e F T pivot a χ color
      (S T pivot (⟨a, ha⟩, color)) θ
    Tendsto f (U : Filter ℕ) (𝓝 (limUnder (U : Filter ℕ) f)) ∧
      0 ≤ limUnder (U : Filter ℕ) f ∧ limUnder (U : Filter ℕ) f ≤ 3*θ + cap := by
  exact hdata.calibration T pivot (⟨a, ha⟩, color) hT hbefore θ hθ

theorem finite_scale_block_calibration_limit {n m r : ℕ}
    (M : ℕ) (e : Fin (2*n) ↪o ℕ) (F : MasterParameterFamily) (U : Ultrafilter ℕ)
    (cap η : ℝ) (B : Finset (Fin n → ℚ)) (A : Finset ℚ)
    (hclosed : FiniteScaleClosure B A) (χ : ℕ → Fin r)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (hdata : PrincipalPredictionLimitData (m := m) M e F U cap η
      (scaleColorFactor A r) χ (scaleColorValue A r) S)
    (b : Fin n → ℚ) (hb : b ∈ B) (T : Finset (Fin n)) (pivot : Fin n)
    (hT : T.Nonempty) (hbefore : ∀ k ∈ T, k < pivot) (color : Fin r)
    (θ : ℝ) (hθ : 0 < θ) :
    let γ := scaleBlockColorIndex B A hclosed b hb (insert pivot T)
      (by simp) color
    let f := principalCalibrationProbability M e F T pivot
      (finiteScaleBlockProduct b (insert pivot T)) χ color (S T pivot γ) θ
    Tendsto f (U : Filter ℕ) (𝓝 (limUnder (U : Filter ℕ) f)) ∧
      0 ≤ limUnder (U : Filter ℕ) f ∧ limUnder (U : Filter ℕ) f ≤ 3*θ + cap := by
  exact hdata.calibration T pivot
    (scaleBlockColorIndex B A hclosed b hb (insert pivot T) (by simp) color)
    hT hbefore θ hθ

theorem finite_scale_chain_count_limits {n m r : ℕ}
    (M : ℕ) (e : Fin (2*n) ↪o ℕ) (F : MasterParameterFamily) (U : Ultrafilter ℕ)
    (cap η : ℝ) (B : Finset (Fin n → ℚ)) (A : Finset ℚ)
    (hclosed : FiniteScaleClosure B A) (χ : ℕ → Fin r)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (hdata : PrincipalPredictionLimitData (m := m) M e F U cap η
      (scaleColorFactor A r) χ (scaleColorValue A r) S)
    (C : PrincipalCoordinateChain n (m+1)) (b : Fin n → ℚ) (hb : b ∈ B)
    (color : Fin r) :
    let γ := fun col => scaleBlockColorIndex B A hclosed b hb (C.block col)
      (by simp [PrincipalCoordinateChain.block]) color
    let a := fun col => finiteScaleBlockProduct b (C.block col)
    let rows := fun col => S (C.tail col) (C.pivot col) (γ col)
    let I := principalWeightedColorCount C M e F a χ (fun _ => color) color
    let E := principalModelColorCount C M e F a χ color rows
    Tendsto E (U : Filter ℕ) (𝓝 (limUnder (U : Filter ℕ) E)) ∧
      limUnder (U : Filter ℕ) E ∈ Set.Icc (0 : ℝ) 1 ∧
      Tendsto I (U : Filter ℕ) (𝓝 (limUnder (U : Filter ℕ) I)) ∧
      Tendsto (fun w => |I w - E w|) (U : Filter ℕ)
        (𝓝 (limUnder (U : Filter ℕ) (fun w => |I w - E w|))) ∧
      limUnder (U : Filter ℕ) (fun w => |I w - E w|) ≤ η ∧
      |limUnder (U : Filter ℕ) I - limUnder (U : Filter ℕ) E| ≤ η := by
  intro γ a rows I E
  have hm : Tendsto E (U : Filter ℕ) (𝓝 (limUnder (U : Filter ℕ) E)) ∧
      limUnder (U : Filter ℕ) E ∈ Set.Icc (0 : ℝ) 1 :=
    hdata.model_counts C γ color
  have hc : Tendsto E (U : Filter ℕ) (𝓝 (limUnder (U : Filter ℕ) E)) ∧
      Tendsto I (U : Filter ℕ) (𝓝 (limUnder (U : Filter ℕ) I)) ∧
      Tendsto (fun w => |I w - E w|) (U : Filter ℕ)
        (𝓝 (limUnder (U : Filter ℕ) (fun w => |I w - E w|))) ∧
      limUnder (U : Filter ℕ) (fun w => |I w - E w|) ∈ Set.Icc (0 : ℝ) η ∧
      |limUnder (U : Filter ℕ) I - limUnder (U : Filter ℕ) E| ≤ η :=
    hdata.weighted_counts C γ color
  exact ⟨hm.1, hm.2, hc.2.1, hc.2.2.1, hc.2.2.2.1.2, hc.2.2.2.2⟩

end Hindman168
