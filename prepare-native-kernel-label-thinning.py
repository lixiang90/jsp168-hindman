from pathlib import Path

source = Path('Hindman168/RoughNativeKernelSpatialPolynomial.lean').read_text(encoding='utf-8')
start = source.index('theorem rough_native_kernel_spatial_log_polynomial')
end = source.index('    (u : κ → ℝ) (K : ℝ) :', start)
header = source[start:end]
header = header.replace('theorem rough_native_kernel_spatial_log_polynomial {κ : Type*}',
    'theorem rough_native_kernel_label_thinning {κ : Type*} [Fintype κ]')
header = header.replace('    (j : ℤ) (hVS', '    (hVS')
variable_start = header.index('    (a m : MvPolynomial')
varying = header[variable_start:]
header = header[:variable_start]
varying = varying.replace('(hp : ∀ x,', '(_hp : ∀ x,').replace('(ha : a.totalDegree', '(_ha : a.totalDegree')
varying = varying.replace('(hm : m.totalDegree', '(_hm : m.totalDegree').replace('(hd : RoughVectorMvDegreeLE', '(_hd : RoughVectorMvDegreeLE')
prefix = '''import Hindman168.RoughNativeKernelSpatialPolynomial
import Hindman168.RoughNativeKernelDegreeBound
import Hindman168.RoughFiniteLabelThinning
import Hindman168.RoughJointProgressionPolynomial

namespace Hindman168
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

'''
conclusion = '''    (K H : ℕ) (hH : 0 < H) :
    ∃ N : ℕ, 0 < N ∧ ∀
''' + varying.rstrip() + ''', ∀ bad : ℕ → ((κ → Fin K) × Fin K) → Prop,
      (∀ z : ℕ, z < N → ∃ label, bad z label) →
      ∃ a0 b : ℕ, ∃ label : (κ → Fin K) × Fin K,
        let u : κ → ℝ := fun k => (label.1 k).val
        let Nnew := roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr (label.2.val : ℤ)
        0 < b ∧ b ≤ N ∧ Module.finrank ℝ Nnew.E < Module.finrank ℝ D.E ∧
        (∀ z : ℕ, z < H → a0+b*z < N ∧ bad (a0+b*z) label) ∧
        ∃ pNew : RoughVectorMvPolynomial (Option κ) Nnew.E,
          RoughVectorMvDegreeLE pNew (roughKernelDegreeFactor s*d) ∧
          ∀ (z : ℝ) (y : κ → ℝ), roughVectorMvEval pNew (Option.elim · z y) =
            nativeLieGlobalLogarithm (E := Nnew.E) (I := Nnew.I)
              (roughNativeKernelMap D S hS χ hχ hQ V hVr (label.2.val : ℤ) hVS hχV a m P hP hchar
                (Option.elim · ((a0 : ℝ)+(b : ℝ)*z) (fun k => u k+(K : ℝ)*y k))) := by
  obtain ⟨N, hN, hthin⟩ := rough_finite_label_thinning H hH ((κ → Fin K) × Fin K)
  refine ⟨N, hN, ?_⟩
  intro a m P hP hchar p hp d ha hm hd bad hbad
  obtain ⟨a0, b, label, hb, hbN, hmono⟩ := hthin bad hbad
  let Nnew := roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr (label.2.val : ℤ)
  let u : κ → ℝ := fun k => (label.1 k).val
  let Qnew : (Option κ → ℝ) → Nnew.G := fun x =>
    roughNativeKernelMap D S hS χ hχ hQ V hVr (label.2.val : ℤ) hVS hχV a m P hP hchar
      (Option.elim · (x none) (fun k => u k+(K : ℝ)*x (some k)))
  obtain ⟨q, hq, heq⟩ := rough_native_kernel_spatial_log_polynomial D S hS χ hχ hQ V hVr
    (label.2.val : ℤ) hVS hχV a m P hP hchar p hp d ha hm hd u (K : ℝ)
  obtain ⟨pNew, hdegree, heNew⟩ := rough_joint_progression_polynomial
    (nativeLieGlobalLogarithm (E := Nnew.E) (I := Nnew.I)) Qnew q
    (roughKernelDegreeFactor s*d) (rough_native_kernel_degree_uniform D hq) heq (a0 : ℝ) (b : ℝ)
  exact ⟨a0, b, label, hb, hbN,
    roughNativeKernelNilmanifold_finrank_lt D S hS χ hχ hQ V hVr _ hVS (by rw [hχV]; norm_num),
    hmono, pNew, hdegree, heNew⟩

end Hindman168
'''
Path('Hindman168/RoughNativeKernelLabelThinning.lean').write_text(prefix+header+conclusion, encoding='utf-8')
