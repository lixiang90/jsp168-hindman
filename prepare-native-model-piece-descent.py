from pathlib import Path

source = Path('Hindman168/RoughNativePieceDescent.lean').read_text(encoding='utf-8')
start = source.index('theorem rough_native_piece_descent')
end = source.index(' := by\n  intro family', start)
header = source[start:end]
header = header.replace('theorem rough_native_piece_descent', 'theorem rough_native_model_piece_descent', 1)
header = header.replace('      let m := map (Rat.castHom ℝ)', '''      M0.natDegree ≤ q → (∀ J ∈ support, (∑ j, J j) ≤ q) →
      P0.natDegree ≤ q → (∀ J ∈ support, (theta J).natDegree+J.sum (fun _ e => e) ≤ q) →
      let m := map (Rat.castHom ℝ)''')
header = header.replace('= eval x a+eval x m),', '= eval x (roughSpatialJointPolynomial support P0 theta)),')
header = header.replace('        (degree : ℕ) (_ha : a.totalDegree ≤ degree) (_hm : m.totalDegree ≤ degree)\n        (_hdegree : RoughVectorMvDegreeLE pLog degree),', '        (_hdegree : RoughVectorMvDegreeLE pLog q),')
header = header.replace('      let Q := fun j : Fin K =>', '''      let hsplit : ∀ x, nativeLieLogarithmCharacter (I := D.I) (G := D.G) χ (P x) = eval x a+eval x m :=
        fun x => by rw [hchar x]; dsimp only [a]; rw [map_sub, sub_add_cancel]
      let Q := fun j : Fin K =>''')
header = header.replace('(j.val : ℤ) hVS hχV a m P hP hchar', '(j.val : ℤ) hVS hχV a m P hP hsplit')
header = header.replace('roughKernelDegreeFactor step*degree', 'roughKernelDegreeFactor step*q')
prefix = '''import Hindman168.RoughNativePieceDescent
import Hindman168.RoughFiniteCoefficientAssembly

namespace Hindman168
open MvPolynomial
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

'''
proof = ''' := by
  intro family
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ j, MetricSpace ((family j).G ⧸ (family j).Γ) := fun j => (family j).metric
  letI : ∀ j, TopologicalSpace ((family j).G ⧸ (family j).Γ) := fun j =>
    (family j).metric.toUniformSpace.toTopologicalSpace
  obtain ⟨N, L, hN, hstage⟩ := rough_native_piece_descent D S hS χ hχ hQ V hVr hVS hχV
    K hK hperiod support d hd A C B hA hC hB Lip hεf hεa
  refine ⟨N, L, hN, ?_⟩
  intro w H q z Z P0 theta M0 M hmodels hz hZ h0 hconst l r hlen hside hl hr F hF hbound
    hM0 he hP0 htheta m a P hP hchar pLog hpLog hdegree hsplit Q
  have hm : m.totalDegree ≤ q := rough_models_joint_real_degree support theta M0 M hmodels hM0 he
  have hn : (-m).totalDegree ≤ q := by simpa only [totalDegree_neg] using hm
  have ha : a.totalDegree ≤ q := by
    dsimp only [a]
    rw [sub_eq_add_neg]
    exact (totalDegree_add _ _).trans
      (max_le (roughSpatialJointPolynomial_degree support P0 theta q hP0 htheta) hn)
  exact hstage w H q z Z P0 theta M0 M hmodels hz hZ h0 hconst l r hlen hside hl hr F hF hbound
    P hP hsplit pLog hpLog q ha hm hdegree

end Hindman168
'''
Path('Hindman168/RoughNativeModelPieceDescent.lean').write_text(prefix+header+proof, encoding='utf-8')
