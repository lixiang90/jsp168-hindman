from pathlib import Path

source = Path('Hindman168/SelectedColorPredictionTolerance.lean').read_text(encoding='utf-8')
head, _ = source.split(' := by\n', 1)
head = ('import Hindman168.SelectedColorPredictionTolerance\n'
        'import Hindman168.MaskColorProductMasks\n\n'
        'namespace Hindman168\nopen Filter FiniteMass MaskOriginalSampling\n'
        'open scoped BigOperators Topology Classical\nuniverse u\n\n'
        '/-- The same calibrated selected model family counts all original\n'
        'product-color masks, including singleton masks, at the prescribed\n'
        'counting tolerance. Inverse existence remains explicit and unproved. -/\n' +
        head[head.index('theorem selected_color_prediction_tolerance'):])
head = head.replace('selected_color_prediction_tolerance', 'selected_color_product_counting', 1)
needle = '                        (b w) (fun col => (C.sampleProducts hCrange x col : ℤ)))| < countTolerance)) ∧\n'
assert head.count(needle) == 1
extra = '''              (∀ (γ : Fin (m+1) → ι) (productColor : Fin r), ∀ᶠ w in (U : Filter ℕ),
                |maskOriginalSubsetCorrelation gap (fun col => a (γ col)) (fun _ => C) w
                    (maskCenterAndRows gap (fun _ => C) w
                      (fun col => maskChainColorWeight m hM C hCrange
                        (fun col => a (γ col)) χ (fun col => color (γ col)) col w))
                    (maskColorProductMask (N := M) (fun col => a (γ col)) (fun _ => C) χ productColor w) -
                  expectation (globalRawMass (F.cutoff w) (primorial w) M)
                    (fun x => maskBoundedCountIntegrand gap (fun col => a (γ col)) (fun _ => C) w
                      (fun col => (model (principalTailPositions e (C.tail col)) (p col) (γ col)).val w)
                      (maskColorProductMask (N := M) (fun col => a (γ col)) (fun _ => C) χ productColor w)
                      (fun col => (C.sampleProducts hCrange x col : ℤ)))| < countTolerance)) ∧
'''
head = head.replace(needle, needle.replace('countTolerance)) ∧', 'countTolerance) ∧') + extra, 1)
proof = ''' := by
  obtain ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, hN⟩ :=
    selected_color_prediction_tolerance.{u} ι r n m s hinverse cap hcap countTolerance hcountTolerance
  refine ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, ?_⟩
  intro M hM hNM gap₀ F a ha χ color
  obtain ⟨f, hf, hd, hselected⟩ := hN M hM hNM a ha χ color
  refine ⟨f, hf, hd, ?_⟩
  intro U hU
  obtain ⟨e, heM, model, hmodel, htest, hcal, hrawcal, hchains, hcommon⟩ := hselected U hU
  refine ⟨e, heM, model, hmodel, htest, hcal, hrawcal, ?_, hcommon⟩
  intro C hC
  obtain ⟨p, hp, hpivot, htail, hquality, hcorr, hreplace, hcountslack, hcount⟩ := hchains C hC
  refine ⟨p, hp, hpivot, htail, hquality, hcorr, hreplace, hcountslack, hcount, ?_⟩
  intro γ productColor
  exact hcount γ _ (Eventually.of_forall (fun w V _ y =>
    (maskColorProductMask_unit (N := M) (fun col => a (γ col)) (fun _ => C)
      χ productColor w V y).2))

end Hindman168
'''
Path('Hindman168/SelectedColorProductCounting.lean').write_text(head+proof, encoding='utf-8')
print('Wrote SelectedColorProductCounting; retained proof sources unchanged.')
