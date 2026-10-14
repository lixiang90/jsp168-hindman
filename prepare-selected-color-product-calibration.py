from pathlib import Path

source = Path('Hindman168/SelectedColorBlockCoarseTesting.lean').read_text(encoding='utf-8')
head, body = source.split(' := by\n', 1)
start = head.index('theorem selected_color_block_coarse_testing')
head = ('import Hindman168.MaskColorProductCalibration\n'
        'import Hindman168.SelectedColorBlockCoarseTesting\n\n'
        'namespace Hindman168\nopen FiniteMass Filter\n'
        'open scoped Topology Classical\nuniverse u\n\n'
        '/-- Calibration on the actual product law at a selected block.\n'
        'The same model is represented and approximates the own coarse projection. -/\n'
        + head[start:])
head = head.replace('selected_color_block_coarse_testing', 'selected_color_block_product_calibration', 1)
needle = '    (τ : ℝ)\n'
assert head.count(needle) == 1
head = head.replace(needle, '''    (hmodel : NativePieceRepresented.{u} s (maskGeneratedMaster m (fun _ => ⟨0, hM⟩))
      (masterGapIndex M hM (energyPadding e b)) (fun w y => model.val w y))
    (hm : ∀ w y, 0 ≤ model.val w y)
    (ε : ℝ)
''', 1)
head = head.replace('hilbertFamilyToCompletion _ U model‖ < τ)', 'hilbertFamilyToCompletion _ U model‖ < ε)', 1)
left = head.index('    (v : ℕ → ℤ → ℝ)')
head = head[:left] + '''    (τ : ℝ) (hτ : 0 < τ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ w in (U : Filter ℕ),
      event (originalBlockProductMass (maskGeneratedMaster m (fun _ => ⟨0, hM⟩))
        (T.image (energyPrincipal e)) (energyPrincipal e b) hT
        (fun y hy => Finset.mem_range.mpr (hbefore y hy)) w)
        (fun y => 0 < y ∧ χ (masterColumnCoefficient M (fun _ : Fin 1 => a γ)
          (fun _ _ => insert (energyPrincipal e b) (T.image (energyPrincipal e))) w 0 * y.toNat) = color γ ∧
          model.val w y ≤ 2*τ) < 3*τ + ε + η'''
proof = body[:body.index('  let vg')]
proof += '''  exact maskColorBlock_product_calibration m s hM (T.image (energyPrincipal e)) i hT
    (fun y hy => Finset.mem_range.mpr (hbefore y hy)) (a γ) χ (color γ) U hU
    (f _ _ γ) model (hf _ _ γ) (hd _ _ _ _ γ) ⟨l, htail, hgap⟩ hmodel hm
    ε happrox τ hτ η hη

end Hindman168
'''
Path('Hindman168/SelectedColorBlockProductCalibration.lean').write_text(head+' := by\n'+proof, encoding='utf-8')

source = Path('Hindman168/SelectedColorNativeTestingModels.lean').read_text(encoding='utf-8')
head, _ = source.split(' := by\n', 1)
start = head.index('theorem selected_color_native_testing_models')
head = ('import Hindman168.SelectedColorBlockProductCalibration\n'
        'import Hindman168.SelectedColorNativeTestingModels\n\n'
        'namespace Hindman168\nopen Filter FiniteMass MaskOriginalSampling\n'
        'open scoped BigOperators Topology Classical\nuniverse u\n\n'
        '/-- One selected model family provides original product calibration,\n'
        'coarse native testing and subset-count replacement. Inverse existence\n'
        'remains an explicit hypothesis. Calibration threshold and approximation\n'
        'accuracy are separate parameters. -/\n' + head[start:])
head = head.replace('selected_color_native_testing_models', 'selected_color_calibrated_models', 1)
needle = '          (∀ C : Chain (m+1),'
assert head.count(needle) == 1
calibration = '''          (∀ (T : Finset (Fin n)) (b : Fin n) (γ : ι),
            ∀ hT : (T.image (energyPrincipal e)).Nonempty,
            ∀ hbefore : ∀ y ∈ T.image (energyPrincipal e), y < energyPrincipal e b,
            ∀ θ : ℝ, 0 < θ → ∀ η : ℝ, 0 < η → ∀ᶠ w in (U : Filter ℕ),
              event (originalBlockProductMass F (T.image (energyPrincipal e)) (energyPrincipal e b)
                hT (fun y hy => Finset.mem_range.mpr (hbefore y hy)) w)
                (fun y => 0 < y ∧ χ (masterColumnCoefficient M (fun _ : Fin 1 => a γ)
                  (fun _ _ => insert (energyPrincipal e b) (T.image (energyPrincipal e))) w 0 * y.toNat) = color γ ∧
                  (model T b γ).val w y ≤ 2*θ) < 3*θ + τ + η) ∧
'''
head = head.replace(needle, calibration+needle, 1)
proof = ''' := by
  obtain ⟨J, hJ, κ, τ, hκ, hτ, hsmall, N, hN⟩ :=
    selected_color_native_testing_models.{u} ι r n m s hinverse ε hε
  refine ⟨J, hJ, κ, τ, hκ, hτ, hsmall, N, ?_⟩
  intro M hM hNM gap₀ F a ha χ color
  obtain ⟨f, hf, hd, hselected⟩ := hN M hM hNM a ha χ color
  refine ⟨f, hf, hd, ?_⟩
  intro U hU
  obtain ⟨e, heM, model, hmodel, htest, hchains, hcommon⟩ := hselected U hU
  refine ⟨e, heM, model, hmodel, htest, ?_, hchains, hcommon⟩
  intro T b γ hT hbefore θ hθ η hη
  exact selected_color_block_product_calibration ι m s hM a χ color f hf hd U hU e heM
    T b γ hT hbefore (model T b γ) (hmodel T b γ).1
    (fun w y => ((hmodel T b γ).2.1 w y).1) τ (hmodel T b γ).2.2 θ hθ η hη

end Hindman168
'''
Path('Hindman168/SelectedColorCalibratedModels.lean').write_text(head+proof, encoding='utf-8')
print('Wrote both selected product calibration modules; retained sources unchanged.')
