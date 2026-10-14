from pathlib import Path

source = Path('Hindman168/MaskColorCoarseCalibration.lean').read_text(encoding='utf-8')
head, _ = source.split(' := by\n', 1)
start = head.index('theorem maskColorBlock_coarse_calibration')
head = ('import Hindman168.MaskColorCoarseCalibration\n'
        'import Hindman168.OriginalBlockProductTesting\n\n'
        'namespace Hindman168\nopen FiniteMass Filter\n'
        'open scoped Topology Classical\nuniverse u\n\n'
        '/-- Actual block-product calibration. The original sampling law,\n'
        'color coefficient and chosen coarse model are retained. -/\n' + head[start:])
head = head.replace('maskColorBlock_coarse_calibration', 'maskColorBlock_product_calibration', 1)
start = head.index('    ∀ᶠ w in (U : Filter ℕ),')
head = head[:start] + '''    ∀ᶠ w in (U : Filter ℕ),
      event (originalBlockProductMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) T i.val hT hTi w)
        (fun y => 0 < y ∧
          χ (masterColumnCoefficient N (fun _ : Fin 1 => a)
            (fun _ _ => insert i.val T) w 0 * y.toNat) = c ∧ model.val w y ≤ 2*τ) <
      3*τ + ε + η'''
body = ''' := by
  have hhalf : 0 < η / 2 := half_pos hη
  have hc := maskColorBlock_coarse_calibration m s hN T i hT hTi a χ c U hU
    f model hf hd l hmodel hm ε happrox τ hτ (η / 2) hhalf
  have hF := maskGeneratedMaster_conditions m (fun _ => ⟨0, hN⟩) ∅ (by simp)
  have hp := hU (hF.block_product_testing_uniform T i hT hTi (η / 2) hhalf)
  filter_upwards [hc, hp] with w hcw hpw
  let E (y : ℤ) := 0 < y ∧
    χ (masterColumnCoefficient N (fun _ : Fin 1 => a)
      (fun _ _ => insert i.val T) w 0 * y.toNat) = c ∧ model.val w y ≤ 2*τ
  let φ (y : ℤ) : ℝ := if E y then 1 else 0
  have hb : ∀ y, |φ y| ≤ 1 := by intro y; dsimp [φ]; split_ifs <;> norm_num
  have ht := hpw φ hb
  have he : expectation
      (integerMass ((maskGeneratedMaster m (fun _ => ⟨0, hN⟩)).cutoff w i.val) (primorial w))
      (fun y => masterPredictionBlockMask (maskGeneratedMaster m (fun _ => ⟨0, hN⟩))
        (fun _ => maskBlockChain T i.val hT hTi) (fun _ => 0) w y * φ y) =
    expectation (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) i.val w)
      (fun y => if model.val w y ≤ 2*τ then maskBlockColorWeight m hN T i hT hTi a χ c w y else 0) := by
    congr 1
    funext y
    by_cases hy : 0 < y
    <;> by_cases hcolor : χ (masterColumnCoefficient N (fun _ : Fin 1 => a)
      (fun _ _ => insert i.val T) w 0 * y.toNat) = c
    <;> by_cases hlow : model.val w y ≤ 2*τ
    <;> simp [φ, E, maskBlockColorWeight, maskBlockColorIndicator, hy, hcolor, hlow]
  rw [he] at ht
  rw [event_eq_expectation]
  have hh := le_abs_self
    (expectation (originalBlockProductMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) T i.val hT hTi w) φ -
      expectation (originalPivotMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) i.val w)
        (fun y => if model.val w y ≤ 2*τ then maskBlockColorWeight m hN T i hT hTi a χ c w y else 0))
  have hfinal : expectation (originalBlockProductMass (maskGeneratedMaster m (fun _ => ⟨0, hN⟩))
      T i.val hT hTi w) φ < 3*τ + ε + η := by linarith
  apply lt_of_eq_of_lt ?_ hfinal
  congr 1
  funext y
  dsimp [φ, E]
  split_ifs <;> simp_all

end Hindman168
'''
Path('Hindman168/MaskColorProductCalibration.lean').write_text(head+body, encoding='utf-8')
print('Wrote MaskColorProductCalibration.lean; retained sources unchanged.')
