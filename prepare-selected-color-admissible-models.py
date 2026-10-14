from pathlib import Path

source = Path('Hindman168/SelectedColorProductCounting.lean').read_text(encoding='utf-8')
head, _ = source.split(' := by\n', 1)
head = ('import Hindman168.SelectedColorProductCounting\n'
        'import Hindman168.SelectedAdmissibleParameters\n\n'
        'namespace Hindman168\nopen Filter FiniteMass MaskOriginalSampling\n'
        'open scoped BigOperators Topology Classical\nuniverse u\n\n'
        '/-- The identical selected model witnesses also carry the actual\n'
        'admissible parameters. Native inverse existence remains explicit. -/\n' +
        head[head.index('theorem selected_color_product_counting'):])
head = head.replace('selected_color_product_counting', 'selected_color_admissible_models', 1)
needle = '      ∃ e : Fin (2 * n) ↪o ℕ, ∃ heM : ∀ j, e j < M,\n'
assert head.count(needle) == 1
head = head.replace(needle, needle + '        SelectedAdmissibleFamily M e F ∧\n', 1)
proof = ''' := by
  obtain ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, hN⟩ :=
    selected_color_product_counting.{u} ι r n m s hinverse cap hcap countTolerance hcountTolerance
  refine ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, ?_⟩
  intro M hM hNM gap₀ F a ha χ color
  obtain ⟨f, hf, hd, hselected⟩ := hN M hM hNM a ha χ color
  refine ⟨f, hf, hd, ?_⟩
  intro U hU
  obtain ⟨e, heM, model, hmodel, htest, hcal, hrawcal, hchains, hcommon⟩ := hselected U hU
  have hF := maskGeneratedMaster_conditions m gap₀ ∅ (by simp)
  exact ⟨e, heM, hF.selected_admissible_family e heM,
    model, hmodel, htest, hcal, hrawcal, hchains, hcommon⟩

end Hindman168
'''
Path('Hindman168/SelectedColorAdmissibleModels.lean').write_text(head+proof, encoding='utf-8')
print('Wrote SelectedColorAdmissibleModels; retained proof sources unchanged.')
