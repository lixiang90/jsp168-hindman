from pathlib import Path

s = Path('Hindman168/RoughNativeProjectedObstructionBadFamily.lean').read_text(encoding='utf-8')
head = s[:s.index(' := by\n')]
head = 'import Hindman168.RoughNativeProjectedObstructionBadFamily\nimport Hindman168.RoughNativeCharacterNormalization\n'+head
head = head.replace('theorem rough_native_projected_obstruction_bad_family',
    'theorem rough_native_normalized_obstruction_bad_family')
start = head.index('    (hQ : ∀ x ∈ ')
end = head.index('    (q : ℕ)', start)
head = head[:start]+'''    (hΓ : ∀ g ∈ D.Γ, ∃ n : ℤ,
      nativeLieLogarithmCharacter (I := D.I) (G := D.G) χ g = (n : ℝ))
    (v : D.E) (hv : v ∈ nativeLieSubalgebraModel S) (hχv : χ v ≠ 0)
'''+head[end:]
start = head.index('    let s := ')
head = head[:start]+'''    let hQ := rough_native_integral_character_rational_on_span (I := D.I) D.Γ χ hΓ
    ∃ V : D.E, ∃ hVr : V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      V ∈ nativeLieSubalgebraModel S ∧ χ V = 1 ∧
      ∃ K : ℕ, 0 < K ∧
        nativeLieExponential (I := D.I) (G := D.G) ((K : ℝ) • V) ∈ D.Γ ∧
'''+head[start:]
proof = ''' := by
  intro hQ
  obtain ⟨V, hVS, hVr, hχV, K, hK, hperiod⟩ :=
    rough_native_fixed_character_normalization (I := D.I) D.Γ S hS χ hQ hv hχv
  refine ⟨V, hVr, hVS, hχV, K, hK, hperiod, ?_⟩
  exact rough_native_projected_obstruction_bad_family D S hS χ hχ hQ V hVr hVS hχV
    K hK hperiod q A0 C B hA0 hC hB Lip c η hc hη Scale Z hScale hr

end Hindman168
'''
Path('Hindman168/RoughNativeNormalizedObstructionBadFamily.lean').write_text(head+proof, encoding='utf-8')
