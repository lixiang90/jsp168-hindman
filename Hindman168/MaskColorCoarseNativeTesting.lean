import Hindman168.MaskColorBlockNativeTesting
import Hindman168.NativeCoarseProjectionTesting

/-! Coarse native testing for the original color weight and the same
chosen coarse model. Dense-model testing and projection approximation
are both proved in their original laws; no inverse input is needed here. -/

namespace Hindman168
open FiniteMass Filter
open scoped Topology Classical
universe u

theorem maskColorBlock_coarse_native_testing {r N : ℕ}
    (m s : ℕ) (hN : 0 < N) (T : Finset ℕ) (i : Fin N)
    (hT : T.Nonempty) (hTi : T ⊆ Finset.range i.val)
    (a : ℚ) (χ : ℕ → Fin r) (c : Fin r)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f model v : boundedHilbertFamilies (fun w => FiniteMassL2
      (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) i.val w)))
    (hf : ∀ w y, 0 ≤ f.val w y ∧ f.val w y ≤ 1)
    (hd : MaskColorBlockDualControl m (s+1) hN T i hT hTi a χ c
      (fun w y => f.val w y))
    (l : MaskValidBlockGap T i)
    (hv : NativePieceRepresented.{u} s (maskGeneratedMaster m (fun _ => ⟨0, hN⟩))
      (fun _ => l.val) (fun w y => v.val w y))
    (hb : ∀ w y, y ∈ (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) i.val w).support →
      |v.val w y| ≤ 1)
    (τ : ℝ)
    (happrox : ‖(nativeNilHilbertSubspace.{u} s (maskGeneratedMaster m (fun _ => ⟨0, hN⟩))
        (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) i.val) U
        (fun _ => l.val)).starProjection (hilbertFamilyToCompletion _ U f) -
      hilbertFamilyToCompletion _ U model‖ < τ)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ w in (U : Filter ℕ),
      |expectation (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) i.val w)
        (fun y => (maskBlockColorWeight m hN T i hT hTi a χ c w y - model.val w y) * v.val w y)| < τ + η := by
  have hhalf : 0 < η / 2 := half_pos hη
  have ht := maskColorBlockDualControl_native_testing m s hN T i hT hTi a χ c
    (fun w y => f.val w y) hf hd l (fun w y => v.val w y) hv
  have hr := hU (ht.abs.eventually (Iio_mem_nhds (by simpa only [abs_zero] using hhalf)))
  have hm := nativeCoarseProjection_expectation_testing s
    (maskGeneratedMaster m (fun _ => ⟨0, hN⟩))
    (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) i.val) U (fun _ => l.val)
    (fun _ => integerMass_total_le_one _ _) f model v hv hb τ happrox (η / 2) hhalf
  filter_upwards [hr, hm] with w hrw hmw
  have he : expectation (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) i.val w)
      (fun y => (maskBlockColorWeight m hN T i hT hTi a χ c w y - model.val w y) * v.val w y) =
    expectation (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) i.val w)
      (fun y => (maskBlockColorWeight m hN T i hT hTi a χ c w y - f.val w y) * v.val w y) +
    expectation (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) i.val w)
      (fun y => (f.val w y - model.val w y) * v.val w y) := by
    rw [← expectation_add]
    congr 1
    funext y
    ring
  rw [he]
  have hh := abs_add_le
    (expectation (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) i.val w)
      (fun y => (maskBlockColorWeight m hN T i hT hTi a χ c w y - f.val w y) * v.val w y))
    (expectation (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) i.val w)
      (fun y => (f.val w y - model.val w y) * v.val w y))
  linarith

end Hindman168
