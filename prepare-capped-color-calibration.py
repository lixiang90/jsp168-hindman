from pathlib import Path

chain = [
    ('FiniteOrderNativeShortCubeModels', 'finite_order_native_shortCube_models', 'η'),
    ('FiniteOrderNativeChainPrediction', 'finite_order_native_chain_prediction', 'η'),
    ('SelectedNativeMaskCorrelation', 'selected_native_mask_original_correlations', 'ε'),
    ('SelectedColorDenseNativeModels', 'selected_color_dense_native_models', 'ε'),
    ('SelectedColorNativeTestingModels', 'selected_color_native_testing_models', 'ε'),
    ('SelectedColorCalibratedModels', 'selected_color_calibrated_models', 'ε'),
]

def replace_once(source, old, new):
    assert source.count(old) == 1, (old, source.count(old))
    return source.replace(old, new, 1)

for index, (module, theorem, tolerance) in enumerate(chain):
    source = Path('Hindman168/' + module + '.lean').read_text(encoding='utf-8')
    source = replace_once(source, 'theorem '+theorem+' ', 'theorem '+theorem+'_capped ')
    source = replace_once(source, '    ('+tolerance+' : ℝ) (h'+tolerance+' : 0 < '+tolerance+') :',
        '    (cap : ℝ) (hcap : 0 < cap)\n    ('+tolerance+' : ℝ) (h'+tolerance+' : 0 < '+tolerance+') :')
    error = 'ε' if index < 2 else 'τ'
    source = replace_once(source, '0 < '+error+' ∧ 2 * '+error+' < κ ∧',
        '0 < '+error+' ∧ '+error+' < cap ∧ 2 * '+error+' < κ ∧')
    # Transport the new witness through each existential conclusion.
    source = source.replace('κ, '+error+', hκ, h'+error+', hsmall',
                            'κ, '+error+', hκ, h'+error+', hcap_error, hsmall')
    if index == 0:
        source = replace_once(source, '  let ε := κ / 4', '  let ε := min (κ / 4) (cap / 2)')
        source = replace_once(source,
            '  have hsmall : 2 * ε < κ := by dsimp only [ε]; linarith',
            '''  have hcap_error : ε < cap := by
    have hle : ε ≤ cap / 2 := min_le_right _ _
    linarith
  have hsmall : 2 * ε < κ := by
    have hle : ε ≤ κ / 4 := min_le_left _ _
    linarith''')
    else:
        previous_module, previous_theorem, _ = chain[index-1]
        import_line = 'import Hindman168.'+previous_module
        capped_import = import_line+'Capped'
        if import_line in source.splitlines():
            source = replace_once(source, import_line+'\n', capped_import+'\n')
        else:
            source = capped_import+'\n'+source
        source = replace_once(source, previous_theorem+'.{u}', previous_theorem+'_capped.{u}')
        if index == 2:
            source = replace_once(source,
                '(fun q => hinverse q.val (Nat.le_of_lt_succ q.isLt)) δ hδ',
                '(fun q => hinverse q.val (Nat.le_of_lt_succ q.isLt)) cap hcap δ hδ')
        else:
            source = replace_once(source, 'hinverse '+tolerance+' h'+tolerance,
                                  'hinverse cap hcap '+tolerance+' h'+tolerance)
    note = ('/- The coarse approximation accuracy is additionally capped by a prescribed\n'
            'positive tolerance before N, preserving all original chosen-model properties.\n'
            'The interval inverse existence hypotheses remain explicit. -/\n')
    source = source.replace('theorem '+theorem+'_capped ', note+'theorem '+theorem+'_capped ', 1)
    Path('Hindman168/'+module+'Capped.lean').write_text(source, encoding='utf-8')

source = Path('Hindman168/SelectedColorCalibratedModelsCapped.lean').read_text(encoding='utf-8')
head, _ = source.split(' := by\n', 1)
start = head.index('theorem selected_color_calibrated_models_capped')
head = ('import Hindman168.SelectedColorCalibratedModelsCapped\n\n'
        'namespace Hindman168\nopen Filter FiniteMass MaskOriginalSampling\n'
        'open scoped BigOperators Topology Classical\nuniverse u\n\n'
        '/-- The requested calibration tolerance is fixed before the master count.\n'
        'The same selected models have product calibration below 3*threshold + cap,\n'
        'with no residual approximation term in that bound. Inverse existence\n'
        'remains an explicit hypothesis. -/\n' + head[start:])
head = replace_once(head, 'selected_color_calibrated_models_capped', 'selected_color_calibration_tolerance')
head = replace_once(head, '∀ θ : ℝ, 0 < θ → ∀ η : ℝ, 0 < η → ∀ᶠ w in (U : Filter ℕ),',
                    '∀ θ : ℝ, 0 < θ → ∀ᶠ w in (U : Filter ℕ),')
head = replace_once(head, '< 3*θ + τ + η) ∧', '< 3*θ + cap) ∧')
proof = ''' := by
  obtain ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, hN⟩ :=
    selected_color_calibrated_models_capped.{u} ι r n m s hinverse cap hcap ε hε
  refine ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, ?_⟩
  intro M hM hNM gap₀ F a ha χ color
  obtain ⟨f, hf, hd, hselected⟩ := hN M hM hNM a ha χ color
  refine ⟨f, hf, hd, ?_⟩
  intro U hU
  obtain ⟨e, heM, model, hmodel, htest, hcal, hchains, hcommon⟩ := hselected U hU
  refine ⟨e, heM, model, hmodel, htest, ?_, hchains, hcommon⟩
  intro T b γ hT hbefore θ hθ
  have ht := hcal T b γ hT hbefore θ hθ (cap-τ) (sub_pos.mpr hcap_error)
  filter_upwards [ht] with w hw
  linarith

end Hindman168
'''
Path('Hindman168/SelectedColorCalibrationTolerance.lean').write_text(head+proof, encoding='utf-8')
print('Wrote seven capped calibration modules; retained proof sources unchanged.')
