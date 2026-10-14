from pathlib import Path

source = Path('Hindman168/RoughNativeBadIndex.lean').read_text(encoding='utf-8')
start = source.index('def RoughNativeBadIndex')
end = source.index('\ntheorem rough_native_bad_index_mono')
body = source[start:end].replace('RoughNativeBadIndex', 'RoughNativeComplexBadIndex')
body = body.replace('(D.G ⧸ D.Γ) → ℝ)', '(D.G ⧸ D.Γ) → ℂ)')
body = body.replace('|F x|', '‖F x‖')
body = body.replace('η < |FiniteMass.expectation', 'η < ‖FiniteMass.complexExpectation')
body = body.replace('FiniteMass.expectation', 'FiniteMass.complexExpectation')
body = body.rstrip()
assert body.endswith('|')
body = body[:-1]+'‖\n'
header = '''import Hindman168.RoughNativeBadIndex
import Hindman168.ComplexRealObservable

namespace Hindman168
open scoped Classical
universe u

'''
proof = '''
theorem rough_native_complex_bad_index_real {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (Q : (Option κ → ℝ) → D.G)
    (z t : ℕ) (Z c C : ℝ) (L : NNReal) (B η : ℝ)
    (h : RoughNativeComplexBadIndex D Q z t Z c C L B η) :
    RoughNativeBadIndex D Q z t Z c C L B (η/2) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨lo, hi, v, F, hL, hB, hbox, hstep, hfull, hbad⟩ := h
  obtain ⟨G, hGL, hGB, hdisc⟩ := complex_discrepancy_real_observable
    (FiniteMass.uniformFinsetMass (alignmentBoxClass lo hi v t))
    (FiniteMass.uniformFinsetMass (Fintype.piFinset (fun j => Finset.Ico (lo j) (hi j))))
    (fun y => QuotientGroup.mk (Q (Option.elim · (z : ℝ) (fun j => (y j : ℝ)))))
    F L B hL hB
  refine ⟨lo, hi, v, G, hGL, hGB, hbox, hstep, hfull, ?_⟩
  exact lt_of_lt_of_le (by linarith [hbad]) hdisc

end Hindman168
'''
Path('Hindman168/RoughNativeComplexBadIndex.lean').write_text(header+body+proof, encoding='utf-8')

source = Path('Hindman168/RoughNativeBadFamily.lean').read_text(encoding='utf-8')
start = source.index('def RoughNativeBadFamily')
end = source.index('\ntheorem rough_native_bad_family_length_mono')
body = source[start:end].replace('RoughNativeBadFamily', 'RoughNativeComplexBadFamily')
body = body.replace('RoughNativeBadIndex', 'RoughNativeComplexBadIndex')
proof = '''
theorem rough_native_complex_bad_family_length_mono {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) {H H' w : ℕ} {Scale Z : ℝ}
    {d : ℕ} {c C : ℝ} {L : NNReal} {B η : ℝ} (hH : H ≤ H')
    (h : RoughNativeComplexBadFamily (κ := κ) D H' w Scale Z d c C L B η) :
    RoughNativeComplexBadFamily (κ := κ) D H w Scale Z d c C L B η := by
  obtain ⟨Q, p, t, diff, hd, hp, hdiff, hsmooth, hbad⟩ := h
  exact ⟨Q, p, t, diff, hd, hp, hdiff, hsmooth, fun z hz => hbad z (hz.trans_le hH)⟩

theorem rough_native_complex_bad_family_real {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H w : ℕ) (Scale Z : ℝ)
    (d : ℕ) (c C : ℝ) (L : NNReal) (B η : ℝ)
    (h : RoughNativeComplexBadFamily (κ := κ) D H w Scale Z d c C L B η) :
    RoughNativeBadFamily (κ := κ) D H w Scale Z d c C L B (η/2) := by
  obtain ⟨Q, p, t, diff, hd, hp, hdiff, hsmooth, hbad⟩ := h
  refine ⟨Q, p, t, diff, hd, hp, hdiff, hsmooth, ?_⟩
  intro z hz
  obtain ⟨hlo, hhi, hrough, hb⟩ := hbad z hz
  exact ⟨hlo, hhi, hrough, rough_native_complex_bad_index_real D Q z (t+diff*z) Z c C L B η hb⟩

theorem rough_native_zero_dimension_no_complex_bad_index {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (hdim : Module.finrank ℝ D.E = 0)
    (Q : (Option κ → ℝ) → D.G) (z t : ℕ) (Z c C : ℝ) (L : NNReal) (B η : ℝ)
    (hη : 0 < η) : ¬ RoughNativeComplexBadIndex D Q z t Z c C L B η := by
  intro h
  exact rough_native_zero_dimension_no_bad_index D hdim Q z t Z c C L B (η/2)
    (by positivity) (rough_native_complex_bad_index_real D Q z t Z c C L B η h)

theorem rough_native_zero_dimension_no_complex_bad_family {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (hdim : Module.finrank ℝ D.E = 0)
    (H w : ℕ) (Scale Z : ℝ) (d : ℕ) (c C : ℝ) (L : NNReal) (B η : ℝ)
    (hH : 0 < H) (hη : 0 < η) :
    ¬ RoughNativeComplexBadFamily (κ := κ) D H w Scale Z d c C L B η := by
  intro h
  exact rough_native_zero_dimension_no_bad_family D hdim H w Scale Z d c C L B (η/2)
    hH (by positivity) (rough_native_complex_bad_family_real D H w Scale Z d c C L B η h)

end Hindman168
'''
header = '''import Hindman168.RoughNativeBadFamily
import Hindman168.RoughNativeComplexBadIndex
import Hindman168.RoughNativeZeroDimension

namespace Hindman168
open scoped Classical
universe u

'''
Path('Hindman168/RoughNativeComplexBadFamily.lean').write_text(header+body+proof, encoding='utf-8')
