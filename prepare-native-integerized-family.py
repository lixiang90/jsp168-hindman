from pathlib import Path

src = Path('Hindman168/RoughNativeAsymptoticModelBadFamily.lean').read_text(encoding='utf-8')
prefix = src[:src.index('theorem rough_native_asymptotic_model_bad_family')]
prefix = prefix.replace('namespace Hindman168', 'import Hindman168.RoughNativeAsymptoticModelBadFamily\nimport Hindman168.RoughNativeJointCoefficientThinning\n\nnamespace Hindman168')
head = src[src.index('theorem rough_native_asymptotic_model_bad_family'):src.index(' := by\n  intro family')]
head = head.replace('theorem rough_native_asymptotic_model_bad_family', 'theorem rough_native_integerized_bad_family')
head = head.replace('    (c η : ℝ)', '    (q : ℕ) (c η : ℝ)')
head = head.replace('∀ (q t diff : ℕ)', '∀ (t diff : ℕ)')
head = head.replace('(M0 : Polynomial ℚ) (M :', '(M :')
start = head.index('        (∀ z : ℕ, z < N → ∃ n : ℤ, M0.eval')
end = head.index('        ∀ (lo hi a0 :', start)
head = head[:start]+head[end:]
head = head.replace('          M0.natDegree ≤ q → ', '          ')
proof = ''' := by
  intro family
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ j, MetricSpace ((family j).G ⧸ (family j).Γ) := fun j => (family j).metric
  letI : ∀ j, TopologicalSpace ((family j).G ⧸ (family j).Γ) := fun j =>
    (family j).metric.toUniformSpace.toTopologicalSpace
  obtain ⟨Part, L, hPart, hglobal⟩ := rough_native_asymptotic_model_bad_family D S hS χ hχ hQ V hVr hVS hχV
    K hK hperiod support d hd A C B hA hC hB Lip c η hc hη Scale Z hg hScale hZ
  refine ⟨Part, L, hPart, ?_⟩
  intro H hH
  obtain ⟨Len, hLen, hstage⟩ := hglobal H hH
  obtain ⟨N, hN, hthin⟩ := rough_native_joint_coefficient_thinning D support q Len hLen
  refine ⟨N, hN, ?_⟩
  filter_upwards [hstage, eventually_ge_atTop N] with w hw hNw
  intro t diff P0 theta M hmodels lo hi a0 F hmin hside hlo hhi hLip hbound he hP0 htheta
    P hP hchar pLog hpLog hdegree hdiff hsmooth hsize hrough hbad
  obtain ⟨a, b, M0, Pnew, pNew, hb, hbN, hindex, hM0, hden, hval, hmodels', hP0', htheta',
    hformula, hmem, hchar', hdegree', hlog'⟩ :=
    hthin w (Z w) A P0 theta M (nativeLieSubalgebraSubgroup (E := D.E) S)
      (nativeLieLogarithmCharacter (I := D.I) (G := D.G) χ) P hNw hP0 htheta hmodels hP hchar pLog hpLog hdegree
  obtain ⟨hdiff', hsmooth', hsize', hrough'⟩ := rough_progression_reparametrize hdiff hb (hbN.trans hNw)
    hsmooth hsize hrough hindex
  refine hw q (t+diff*a) (diff*b)
    (P0.comp (Polynomial.C (a : ℝ)+Polynomial.C (b : ℝ)*Polynomial.X))
    (fun J => (theta J).comp (Polynomial.C (a : ℝ)+Polynomial.C (b : ℝ)*Polynomial.X)) M0
    (fun J => (M J).comp (Polynomial.C (a : ℚ)+Polynomial.C (b : ℚ)*Polynomial.X))
    hmodels' (fun z hz => (hval z hz).1) (fun z hz => (hval z hz).2)
    (fun z => lo (a+b*z)) (fun z => hi (a+b*z)) (fun z => a0 (a+b*z)) (fun z => F (a+b*z))
    (fun z hz => hmin _ (hindex z hz)) (fun z hz => hside _ (hindex z hz))
    (fun z hz => hlo _ (hindex z hz)) (fun z hz => hhi _ (hindex z hz))
    (fun z hz => hLip _ (hindex z hz)) (fun z hz => hbound _ (hindex z hz))
    hM0 he hP0' htheta' Pnew hmem hchar' pNew hlog' hdegree'
    hdiff' hsmooth' hsize' hrough' ?_
  intro z hz
  have h := hbad (a+b*z) (hindex z hz)
  have hs : (t : ℤ)+(diff : ℤ)*a+(diff : ℤ)*b*z = (t : ℤ)+(diff : ℤ)*((a : ℤ)+(b : ℤ)*z) := by ring
  simpa only [hformula, Option.elim_none, Option.elim_some, Nat.cast_add, Nat.cast_mul, hs] using h

end Hindman168
'''
Path('Hindman168/RoughNativeIntegerizedBadFamily.lean').write_text(prefix+head+proof, encoding='utf-8')
