from pathlib import Path

source = Path('Hindman168/PrincipalPredictionModels.lean').read_text(encoding='utf-8')
head = source[source.index('theorem principal_prediction_models'):].split(' := by\n', 1)[0]
head = head.replace('theorem principal_prediction_models', 'theorem principal_prediction_models_with_limits', 1)
needle = '          (∀ T b a,\n'
assert head.count(needle) == 1
head = head.replace(needle,
    '          PrincipalPredictionLimitData (m := m) M e F U cap countTolerance a χ color\n'
    '            (fun T b γ w y => (model T b γ).val w y) ∧\n' + needle, 1)
body = ''' := by
  obtain ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, hN⟩ :=
    principal_prediction_models.{u} ι r n m s hinverse cap hcap countTolerance hcountTolerance
  refine ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, ?_⟩
  intro M hM hNM gap₀ F a ha χ color
  obtain ⟨f, hf, hd, hselected⟩ := hN M hM hNM a ha χ color
  refine ⟨f, hf, hd, ?_⟩
  intro U hU
  obtain ⟨e, heM, hadmissible, model, hmodel, htest, hcal, hrawcal,
    hprincipalcal, hprincipalcount, hrelcount, hchains, hcommon⟩ := hselected U hU
  have hlimits : PrincipalPredictionLimitData (m := m) M e F U cap countTolerance a χ color
      (fun T b γ w y => (model T b γ).val w y) := by
    apply principal_prediction_limit_data M e F hadmissible.raw_probability U hU cap
      countTolerance a χ color (fun T b γ w y => (model T b γ).val w y)
      (fun T b γ w y => (hmodel T b γ).2.1 w y)
    · exact hprincipalcal
    · exact hprincipalcount
  exact ⟨e, heM, hadmissible, model, hlimits, hmodel, htest, hcal, hrawcal,
    hprincipalcal, hprincipalcount, hrelcount, hchains, hcommon⟩

end Hindman168
'''
header = '''import Hindman168.PrincipalPredictionModels
import Hindman168.PrincipalPredictionLimitData

/-! The same selected models and fixed ultrafilter now carry actual
calibration and complete count limits. Native inverse existence remains
an explicit unproved input; this is not a proof of StrongConjecture. -/

namespace Hindman168
open Filter FiniteMass MaskOriginalSampling
open scoped BigOperators Topology Classical
universe u

'''
Path('Hindman168/PrincipalPredictionModelsWithLimits.lean').write_text(header + head + body, encoding='utf-8')
print('Generated the same-witness prediction model theorem with actual limits.')
