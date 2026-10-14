from pathlib import Path
src=Path('Hindman168/NativeOriginalRealBadPairCharacters.lean').read_text(encoding='utf-8')
start=src.index('theorem native_original_real_bad_pair_characters')
stop=src.index(' := by',start)
header=src[start:stop].replace('native_original_real_bad_pair_characters','native_original_asymptotic_bad_pair_characters')
header=header.replace('(hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B) (hη : 0 < η) :',
'''(hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B) (hη : 0 < η)
    (Scale Z : ℕ → ℝ) (hg : PowerDominates atTop Z Scale)
    (hScale : ∀ᶠ w in atTop, 1 ≤ Scale w) (hZ : ∀ᶠ w in atTop, 0 ≤ Z w) :''')
begin=header.index('      ∃ A Z0 : ℝ,')
end=header.index('      ∀ (Q :',begin)
header=header[:begin]+'''      ∃ A : ℝ, 0 < A ∧ ∀ᶠ w in atTop,
      ∀ t : ℕ, Scale w ≤ t → (t : ℝ) < 2*Scale w →
'''+header[end:]
header=header.replace(' z t Z c C L B η',' z t (Z w) c C L B η').replace('/Z)', '/(Z w))')
result='''import Hindman168.NativeOriginalRealBadPairCharacters
import Hindman168.RoughOriginalBadPairScaleThresholds

/-! ONE fixed original finite character list and coefficient budget now
work eventually for ALL dyadic rough steps, raw sources, boxes and observables.
Actual PowerDominates supplies the thresholds; no production premise remains. -/
namespace Hindman168
open MeasureTheory MvPolynomial Filter
open scoped Manifold ContDiff BigOperators Classical
universe u

'''+header+''' := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨S,hS,A,Z0,hA,hZ0,hProduce⟩ := native_original_real_bad_pair_characters D n d c C B η L hc hC hB hη
  refine ⟨S,hS,A,hA,?_⟩
  filter_upwards [rough_original_bad_pair_scale_thresholds hg hScale hZ c Z0 hc hZ0] with w hw
  intro t htlo hthi Q p hp hQ z hBad
  obtain ⟨ht,hZt,htZ,htc⟩ := hw.2 t htlo hthi
  exact hProduce t ht (Z w) hw.1 hZt htZ htc Q p hp hQ z hBad

end Hindman168
'''
Path('Hindman168/NativeOriginalAsymptoticBadPairCharacters.lean').write_text(result,encoding='utf-8')
