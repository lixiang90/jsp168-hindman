from pathlib import Path

source = Path('Hindman168/FiniteScalePredictionModels.lean').read_text(encoding='utf-8')
head = source[source.index('theorem finite_scale_prediction_models'):].split(' := by\n', 1)[0]
head = head.replace('theorem finite_scale_prediction_models', 'theorem finite_scale_prediction_models_unit_observables', 1)
needle = '                (∀ w p z, |obs w p z| ≤ B) ∧ (∀ w p, LipschitzWith Lip (obs w p)) ∧\n'
assert head.count(needle) == 1
head = head.replace(needle,
    '                (∀ w p z, 0 ≤ obs w p z ∧ obs w p z ≤ 1) ∧\n' + needle, 1)
body = ''' := by
  obtain ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, hN⟩ :=
    finite_scale_prediction_models.{u} A hA r n m s hinverse cap hcap countTolerance hcountTolerance
  refine ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, ?_⟩
  intro M hM hNM gap₀ F a color χ
  obtain ⟨f, hf, hd, hselected⟩ := hN M hM hNM χ
  refine ⟨f, hf, hd, ?_⟩
  intro U hU
  obtain ⟨e, heM, hadmissible, model, hlimits, hmodel, htest, hcal, hrawcal,
    hprincipalcal, hprincipalcount, hrelcount, hchains, hcommon⟩ := hselected U hU
  refine ⟨e, heM, hadmissible, model, hlimits, hmodel, htest, hcal, hrawcal,
    hprincipalcal, hprincipalcount, hrelcount, hchains, ?_⟩
  obtain ⟨G, B, Lip, hB, hreps⟩ := hcommon
  letI := G.metric
  letI : TopologicalSpace (G.G ⧸ G.Γ) := G.metric.toUniformSpace.toTopologicalSpace
  refine ⟨G, B, Lip, hB, ?_⟩
  intro T b γ
  obtain ⟨obs, g, x, hb, hl, he⟩ := hreps T b γ
  obtain ⟨obs', hrange, hb', hl', he'⟩ :=
    piecewise_unit_observables G.Γ F (masterGapIndex M hM (energyPadding e b))
      (fun w y => (model T b γ).val w y) ((hmodel T b γ).2.1) obs g x B Lip hb hl he
  exact ⟨obs', g, x, hrange, hb', hl', he'⟩

end Hindman168
'''
header = '''import Hindman168.FiniteScalePredictionModels
import Hindman168.NativeUnitObservables

/-! All scale/color models use globally unit-range observables on the
same common native quotient, preserving their uniform bounds and exact
values. Native inverse existence is still explicit and unproved. -/

namespace Hindman168
open Filter FiniteMass MaskOriginalSampling
open scoped BigOperators Topology Classical
universe u

'''
Path('Hindman168/FiniteScaleNativeUnitModels.lean').write_text(header + head + body, encoding='utf-8')
print('Generated globally unit-range models on the same common native quotient.')
