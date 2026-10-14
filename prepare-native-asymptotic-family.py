from pathlib import Path
import re

src = Path('Hindman168/RoughNativeModelBadFamily.lean').read_text(encoding='utf-8')
prefix = src[:src.index('theorem rough_native_model_bad_family')]
prefix = prefix.replace('namespace Hindman168', 'import Hindman168.RoughNativeModelBadFamily\nimport Hindman168.RoughNativeDescentBudgets\n\nnamespace Hindman168\nopen Filter')
head = src[src.index('theorem rough_native_model_bad_family'):src.index(' := by\n  intro family')]
head = head.replace('theorem rough_native_model_bad_family', 'theorem rough_native_asymptotic_model_bad_family')
head = head.replace('    {εfreeze εapprox : ℝ} (hεf : 0 < εfreeze) (hεa : 0 < εapprox) :', '''    (c η : ℝ) (hc : 0 < c) (hη : 0 < η) (Scale Z : ℕ → ℝ)
    (hg : PowerDominates atTop Z Scale) (hScale : ∀ᶠ w in atTop, 1 ≤ Scale w)
    (hZ : ∀ᶠ w in atTop, 0 ≤ Z w) :''')
pre, post = head.split('    ∃ Part : ℕ', 1)
post = '    ∃ Part : ℕ'+post
post = post.replace('      ∃ N : ℕ, 0 < N ∧ ∀ (w q t diff : ℕ) (Z Scale c θ η : ℝ)',
    '      ∃ N : ℕ, 0 < N ∧ ∀ᶠ w in atTop, ∀ (q t diff : ℕ)')
post = post.replace('        0 < Z → 1 ≤ Z/K →\n', '')
post = post.replace('          (∀ z : ℕ, z < N → ∀ j, 2*(Part : ℤ) ≤ hi z j-lo z j) →\n          (∀ z : ℕ, z < N → ∀ j, (2*Part*K : ℤ) ≤ hi z j-lo z j) →',
    '          (∀ z : ℕ, z < N → ∀ j, c*Z ≤ (hi z j : ℝ)-lo z j) →')
post = post.replace('          0 < diff → N ≤ w →', '          0 < diff →')
start = post.index('          (∀ z : ℕ, z < N → 0 < t+diff*z')
end = post.index('          (∀ z : ℕ, z < N →\n            η ≤ |', start)
post = post[:start]+post[end:]
post = re.sub(r'\bZ\b', '(Z w)', post)
post = re.sub(r'\bScale\b', '(Scale w)', post)
post = re.sub(r'\bθ\b', '(η/2)', post)
head = pre+post
proof = ''' := by
  intro family
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ j, MetricSpace ((family j).G ⧸ (family j).Γ) := fun j => (family j).metric
  letI : ∀ j, TopologicalSpace ((family j).G ⧸ (family j).Γ) := fun j =>
    (family j).metric.toUniformSpace.toTopologicalSpace
  obtain ⟨Part, L, hPart, hglobal⟩ := rough_native_model_bad_family
    (εfreeze := η/32) (εapprox := η/32) D S hS χ hχ hQ V hVr hVS hχV
    K hK hperiod support d hd A C B hA hC hB Lip (by positivity) (by positivity)
  refine ⟨Part, L, hPart, ?_⟩
  intro H hH
  obtain ⟨N, hN, hstage⟩ := hglobal H hH
  refine ⟨N, hN, ?_⟩
  have hbud := rough_native_descent_budgets (κ := κ) hg hScale hZ Part K N hPart hK c B η hc hB hη
  filter_upwards [hbud] with w hw
  intro q t diff P0 theta M0 M hmodels h0 hconst lo hi a0 F hmin hside hlo hhi
    hLip hbound hM0 he hP0 htheta P hP hchar pLog hpLog hdegree hdiff hsmooth hsize hrough hbad
  have hb := fun z (hz : z < N) => hw.2.2.2 (t+diff*z) (hsize z hz).1 (hsize z hz).2 (hrough z hz)
  have hbox := fun z (hz : z < N) => (hb z hz).2.2.2.2 (lo z) (hi z) (hmin z hz)
  exact hstage w q t diff (Z w) (Scale w) c (η/2) η P0 theta M0 M hmodels hw.2.1 hw.2.2.1
    h0 hconst lo hi a0 F (fun z hz => (hbox z hz).1) (fun z hz => (hbox z hz).2)
    hside hlo hhi hLip hbound hM0 he hP0 htheta P hP hchar pLog hpLog hdegree
    hdiff hw.1 hsmooth hsize hrough (fun z hz => ⟨(hb z hz).1, (hb z hz).2.1⟩)
    hc (fun z hz => (hb z hz).2.2.1) hmin (fun z hz => (hb z hz).2.2.2.1) hbad

end Hindman168
'''
Path('Hindman168/RoughNativeAsymptoticModelBadFamily.lean').write_text(prefix+head+proof, encoding='utf-8')
