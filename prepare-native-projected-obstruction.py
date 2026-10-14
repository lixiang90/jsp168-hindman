from pathlib import Path

source = Path('Hindman168/RoughNativeComplexObstructionBadFamily.lean').read_text(encoding='utf-8')
head = source[:source.index(' := by\n')]
head = 'import Hindman168.RoughNativeScalarExpansion\nimport Hindman168.RoughNativeComplexObstructionBadFamily\n'+head
head = head.replace('theorem rough_native_complex_obstruction_bad_family',
                    'theorem rough_native_projected_obstruction_bad_family')
head = head.replace('(s : Finset (κ → ℕ)) (q : ℕ) (he : ∀ I ∈ s, 0 < (∑ j, I j) ∧ (∑ j, I j) ≤ q)',
                    '(q : ℕ)')
head = head.replace('    let support := roughFiniteMultiindices s',
                    '    let s := roughSpatialDegreeIndices κ q')
head = head.replace('        (P0 : Polynomial ℝ) (theta : (κ →₀ ℕ) → Polynomial ℝ)\n', '')
head = head.replace('          P0.natDegree ≤ q → (∀ J ∈ support, (theta J).natDegree+J.sum (fun _ e => e) ≤ q) →\n', '')
head = head.replace('            (_hP : ∀ x, P x ∈ nativeLieSubalgebraSubgroup (E := D.E) S)\n'
    '            (_hchar : ∀ x, nativeLieLogarithmCharacter (I := D.I) (G := D.G) χ (P x) =\n'
    '              eval x (roughSpatialJointPolynomial support P0 theta)),',
    '            (_hP : ∀ x, P x ∈ nativeLieSubalgebraSubgroup (E := D.E) S),')
head = head.replace('                (roughSpatialFixedPolynomial support (P0.eval (z : ℝ))\n'
                    '                  (fun J => (theta J).eval (z : ℝ))))',
                    '                (roughScalarSpatialProjection χ pLog (z : ℝ)))')
assert 'P0' not in head and 'theta' not in head
proof = ''' := by
  intro s family
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ j, MetricSpace ((family j).G ⧸ (family j).Γ) := fun j => (family j).metric
  letI : ∀ j, TopologicalSpace ((family j).G ⧸ (family j).Γ) := fun j =>
    (family j).metric.toUniformSpace.toTopologicalSpace
  have he : ∀ I ∈ s, 0 < (∑ j, I j) ∧ (∑ j, I j) ≤ q :=
    fun I hI => (rough_spatial_degree_indices_mem q I).mp hI
  obtain ⟨Part, L, hPart, hglobal⟩ := rough_native_complex_obstruction_bad_family
    D S hS χ hχ hQ V hVr hVS hχV K hK hperiod s q he A0 C B hA0 hC hB Lip
    c η hc hη Scale Z hScale hr
  refine ⟨Part, L, hPart, ?_⟩
  intro H hH
  obtain ⟨N, hN, hstage⟩ := hglobal H hH
  refine ⟨N, hN, ?_⟩
  filter_upwards [hstage] with w hw
  intro t diff pOb bOb lo hi a0 F hmin hside hlo hhi hLip hbound
    P hP pLog hpLog hdegree hdiff hsmooth hsize hrough hpOb hbOb hOb hbad
  obtain ⟨P0, theta, hP0, htheta, hchar, hfixed⟩ :=
    rough_native_scalar_expansion D χ P pLog q hdegree hpLog
  refine hw t diff P0 theta pOb bOb lo hi a0 F hmin hside hlo hhi hLip hbound hP0 htheta
    P hP hchar pLog hpLog hdegree hdiff hsmooth hsize hrough hpOb hbOb ?_ hbad
  intro I hI z hz
  have hf : roughScalarSpatialProjection χ pLog (z : ℝ) =
      roughSpatialFixedPolynomial (roughFiniteMultiindices s) (P0.eval (z : ℝ))
        (fun J => (theta J).eval (z : ℝ)) := hfixed (z : ℝ)
  rw [← hf]
  exact hOb I hI z hz

end Hindman168
'''
Path('Hindman168/RoughNativeProjectedObstructionBadFamily.lean').write_text(head+proof, encoding='utf-8')
