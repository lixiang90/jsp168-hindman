from pathlib import Path
import re

source = Path('Hindman168/PrincipalPredictionModelsWithLimits.lean').read_text(encoding='utf-8')
head = source[source.index('theorem principal_prediction_models_with_limits'):].split(' := by\n', 1)[0]
head = head.replace('theorem principal_prediction_models_with_limits (ι : Type*) [Fintype ι]',
    'theorem finite_scale_prediction_models (A : Finset ℚ) (hA : ∀ a ∈ A, 0 < a)', 1)
head = re.sub(r'\bι\b', '(ScaleColorIndex A r)', head)
old_quantifiers = ('      ∀ (a : (ScaleColorIndex A r) → ℚ) (_ha : ∀ γ, 0 < a γ)\n'
    '        (χ : ℕ → Fin r) (color : (ScaleColorIndex A r) → Fin r),\n')
assert head.count(old_quantifiers) == 1
head = head.replace(old_quantifiers,
    '      let a := scaleColorFactor A r\n'
    '      let color := scaleColorValue A r\n'
    '      ∀ χ : ℕ → Fin r,\n', 1)
body = ''' := by
  obtain ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, hN⟩ :=
    principal_prediction_models_with_limits.{u} (ScaleColorIndex A r) r n m s
      hinverse cap hcap countTolerance hcountTolerance
  refine ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, ?_⟩
  intro M hM hNM gap₀ F a color χ
  exact hN M hM hNM a (scaleColorFactor_positive A r hA) χ color

end Hindman168
'''
header = '''import Hindman168.PrincipalPredictionModelsWithLimits
import Hindman168.FiniteScaleColorIndices

/-! A single finite family contains every requested rational scale and
every color. All original outputs, common selected witnesses and fixed
ultrafilter limits are retained. Native inverse existence remains explicit. -/

namespace Hindman168
open Filter FiniteMass MaskOriginalSampling
open scoped BigOperators Topology Classical
universe u

'''
Path('Hindman168/FiniteScalePredictionModels.lean').write_text(header + head + body, encoding='utf-8')
print('Generated the finite scale-and-color specialization with all original outputs.')
