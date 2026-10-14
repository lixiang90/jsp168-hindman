from pathlib import Path

text = Path('Hindman168/NativeRationalFirstLayerOriginalBounds.lean').read_text(encoding='utf-8')
text = text.replace('native_rational_first_layer_original_', 'native_rational_kills_two_original_')
text = text.replace('(nativeRationalFirstLayerIntegerCharacter D L k).toLinearMap', 'f.toLinearMap')
text = text.replace('(k : NativeRationalFirstLayerIndex D L → ℤ)', '''(f : D.E →L[ℝ] ℝ) (hf : L.layer 2 ≤ f.toLinearMap.ker)
    (hInt : ∀ g ∈ D.Γ, ∃ z : ℤ, f (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) = (z : ℝ))''')
text = text.replace('∑ i, (k i : ℝ)*nativeRationalCompactBracketFrequency D L p i', '''f (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1))''')
text = text.replace('  let f := nativeRationalFirstLayerIntegerCharacter D L k\n', '')
text = text.replace('  have hk2 := native_rational_first_layer_integer_character_kills_two D L k\n', '')
text = text.replace('hk2', 'hf')
text = text.replace('fun g => native_rational_first_layer_integer_character_lattice D L k g g.property', 'fun g => hInt g g.property')
text = text.replace('  rw [native_rational_first_layer_integer_character_apply] at he\n', '')
text = text.replace('D L p hp k', 'D L p hp f hf hInt')
text = text.replace('(native_rational_first_layer_integer_character_kills_two D L k)', 'hf')
start = text.index('/-!')
end = text.index('-/', start)+2
text = text[:start]+'''/-! BOTH COMPLETE original raw coefficient tables for ANY actual lattice
character killing TRUE F_2, from its genuine compact first evaluation.
Normalization/integer transport is proved, not restricted to a named family. -/'''+text[end:]
Path('Hindman168/NativeRationalKillsTwoOriginalBounds.lean').write_text(text,encoding='utf-8')
