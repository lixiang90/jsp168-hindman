from pathlib import Path

source = Path('Hindman168/SelectedColorCalibrationTolerance.lean').read_text(encoding='utf-8')
head, _ = source.split(' := by\n', 1)
start = head.index('theorem selected_color_calibration_tolerance')
head = ('import Hindman168.SelectedColorCalibrationTolerance\n'
        'import Hindman168.OriginalBlockRawSampling\n\n'
        'namespace Hindman168\nopen Filter FiniteMass MaskOriginalSampling\n'
        'open scoped BigOperators Topology Classical\nuniverse u\n\n'
        '/-- Calibration at the prescribed tolerance under the complete original\n'
        'global raw-coordinate law. Exact block-product calibration and every\n'
        'other selected model property are retained on the same witnesses.\n'
        'Inverse existence remains an explicit hypothesis. -/\n' + head[start:])
head = head.replace('selected_color_calibration_tolerance', 'selected_color_global_calibration', 1)
needle = '          (∀ C : Chain (m+1),'
assert head.count(needle) == 1
raw = '''          (∀ (T : Finset (Fin n)) (b : Fin n) (γ : ι),
            ∀ hT : (T.image (energyPrincipal e)).Nonempty,
            ∀ hbefore : ∀ y ∈ T.image (energyPrincipal e), y < energyPrincipal e b,
            ∀ θ : ℝ, 0 < θ →
              let i : Fin M := ⟨energyPrincipal e b, heM _⟩
              let hTi : T.image (energyPrincipal e) ⊆ Finset.range i.val :=
                fun y hy => Finset.mem_range.mpr (hbefore y hy)
              let z (x : Fin M → ℕ) : ℤ :=
                ((maskBlockChain (T.image (energyPrincipal e)) i.val hT hTi).sampleProducts
                  (maskBlockChain_block_range (T.image (energyPrincipal e)) i hT hTi) x 0 : ℤ)
              ∀ᶠ w in (U : Filter ℕ),
                event (globalRawMass (F.cutoff w) (primorial w) M)
                  (fun x => 0 < z x ∧ χ (masterColumnCoefficient M (fun _ : Fin 1 => a γ)
                    (fun _ _ => insert (energyPrincipal e b) (T.image (energyPrincipal e))) w 0 * (z x).toNat) = color γ ∧
                    (model T b γ).val w (z x) ≤ 2*θ) < 3*θ + cap) ∧
'''
head = head.replace(needle, raw+needle, 1)
proof = ''' := by
  obtain ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, hN⟩ :=
    selected_color_calibration_tolerance.{u} ι r n m s hinverse cap hcap ε hε
  refine ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, ?_⟩
  intro M hM hNM gap₀ F a ha χ color
  obtain ⟨f, hf, hd, hselected⟩ := hN M hM hNM a ha χ color
  refine ⟨f, hf, hd, ?_⟩
  intro U hU
  obtain ⟨e, heM, model, hmodel, htest, hcal, hchains, hcommon⟩ := hselected U hU
  refine ⟨e, heM, model, hmodel, htest, hcal, ?_, hchains, hcommon⟩
  intro T b γ hT hbefore θ hθ i hTi z
  have hc := hcal T b γ hT hbefore θ hθ
  have hF := maskGeneratedMaster_conditions m gap₀ ∅ (by simp)
  have hr := hU (hF.block_raw_product_event (T.image (energyPrincipal e)) i hT hTi)
  filter_upwards [hc, hr] with w hcw hrw
  calc
    _ = event (originalBlockProductMass F (T.image (energyPrincipal e)) i.val hT hTi w)
        (fun y => 0 < y ∧ χ (masterColumnCoefficient M (fun _ : Fin 1 => a γ)
          (fun _ _ => insert (energyPrincipal e b) (T.image (energyPrincipal e))) w 0 * y.toNat) = color γ ∧
          (model T b γ).val w y ≤ 2*θ) := hrw _
    _ < 3*θ + cap := hcw

end Hindman168
'''
Path('Hindman168/SelectedColorGlobalCalibration.lean').write_text(head+proof, encoding='utf-8')
print('Wrote SelectedColorGlobalCalibration.lean; retained proof sources unchanged.')
