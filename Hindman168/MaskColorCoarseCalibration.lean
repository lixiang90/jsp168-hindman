import Hindman168.MaskColorCoarseNativeTesting
import Hindman168.FiniteCutoffCalibration

namespace Hindman168
open FiniteMass Filter
open scoped Topology Classical
universe u

/-- Weighted calibration of the actual color event using the same native
coarse model and its projection accuracy. No inverse existence is used. -/
theorem maskColorBlock_coarse_calibration {r N : ℕ}
    (m s : ℕ) (hN : 0 < N) (T : Finset ℕ) (i : Fin N)
    (hT : T.Nonempty) (hTi : T ⊆ Finset.range i.val)
    (a : ℚ) (χ : ℕ → Fin r) (c : Fin r)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f model : boundedHilbertFamilies (fun w => FiniteMassL2
      (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) i.val w)))
    (hf : ∀ w y, 0 ≤ f.val w y ∧ f.val w y ≤ 1)
    (hd : MaskColorBlockDualControl m (s+1) hN T i hT hTi a χ c
      (fun w y => f.val w y))
    (l : MaskValidBlockGap T i)
    (hmodel : NativePieceRepresented.{u} s (maskGeneratedMaster m (fun _ => ⟨0, hN⟩))
      (fun _ => l.val) (fun w y => model.val w y))
    (hm : ∀ w y, 0 ≤ model.val w y)
    (ε : ℝ)
    (happrox : ‖(nativeNilHilbertSubspace.{u} s (maskGeneratedMaster m (fun _ => ⟨0, hN⟩))
        (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) i.val) U
        (fun _ => l.val)).starProjection (hilbertFamilyToCompletion _ U f) -
      hilbertFamilyToCompletion _ U model‖ < ε)
    (τ : ℝ) (hτ : 0 < τ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ w in (U : Filter ℕ),
      expectation (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) i.val w)
        (fun y => if model.val w y ≤ 2*τ then maskBlockColorWeight m hN T i hT hTi a χ c w y else 0) <
      3*τ + ε + η := by
  let v w y := calibrationCutoff τ (model.val w y)
  have hb : ∀ w y, |v w y| ≤ 1 := by
    intro w y
    rw [abs_of_nonneg (calibrationCutoff_bounds τ _).1]
    exact (calibrationCutoff_bounds τ _).2
  let vg := masterOriginalBoundedFamily (maskGeneratedMaster m (fun _ => ⟨0, hN⟩))
    (fun _ => i.val) v 1 zero_le_one hb
  have hv := nativePieceRepresented_calibrationCutoff _ (fun _ => l.val) _ hmodel τ hτ
  have ht := maskColorBlock_coarse_native_testing m s hN T i hT hTi a χ c U hU
    f model vg hf hd l hv (fun w y _ => hb w y) ε happrox η hη
  have hr := hU (maskBlockColorWeight_bounds m hN T i hT hTi a χ c)
  filter_upwards [ht, hr] with w htw hrw
  have hc := finite_cutoff_calibration
    (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) i.val w)
    (integerMass_nonnegative _ _) (integerMass_total_le_one _ _)
    (maskBlockColorWeight m hN T i hT hTi a χ c w) (model.val w)
    (fun y => (hrw y).1) (hm w) τ hτ (ε+η) htw
  simpa only [add_assoc] using hc

end Hindman168
