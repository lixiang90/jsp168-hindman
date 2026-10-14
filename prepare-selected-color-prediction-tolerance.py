from pathlib import Path

source = Path('Hindman168/SelectedColorRawCounting.lean').read_text(encoding='utf-8')
head, _ = source.split(' := by\n', 1)
head = ('import Hindman168.SelectedColorRawCounting\n\n'
        'namespace Hindman168\nopen Filter FiniteMass MaskOriginalSampling\n'
        'open scoped BigOperators Topology Classical\nuniverse u\n\n'
        '/-- The complete raw-coordinate counting error is below the prescribed\n'
        'tolerance on the same models that satisfy calibration. Both tolerances\n'
        'are prescribed before the master index count. Inverse existence is\n'
        'still an explicit unproved hypothesis. -/\n' +
        head[head.index('theorem selected_color_raw_counting'):])
head = head.replace('selected_color_raw_counting', 'selected_color_prediction_tolerance', 1)
needle = '    (ε : ℝ) (hε : 0 < ε) :\n'
assert head.count(needle) == 1
head = head.replace(needle, '    (countTolerance : ℝ) (hcountTolerance : 0 < countTolerance) :\n'
    '    let ε : ℝ := countTolerance / (2 * ((Fintype.card (LargeColumnSubset m) : ℝ) + 1))\n', 1)
needle = '                    ((Fintype.card (LargeColumnSubset m) : ℝ) + 1) * ε + η)) ∧\n'
assert head.count(needle) == 1
extra = '''              (∀ (γ : Fin (m+1) → ι)
                (b : ℕ → Finset (Fin (m+1)) → ℤ → ℝ),
                (∀ᶠ w in (U : Filter ℕ),
                  ∀ V ∈ (Finset.univ : Finset (Fin (m+1))).powerset.erase ∅,
                    ∀ y, |b w V y| ≤ 1) → ∀ᶠ w in (U : Filter ℕ),
                  |maskOriginalSubsetCorrelation gap (fun col => a (γ col)) (fun _ => C) w
                    (maskCenterAndRows gap (fun _ => C) w
                      (fun col => maskChainColorWeight m hM C hCrange
                        (fun col => a (γ col)) χ (fun col => color (γ col)) col w)) (b w) -
                    expectation (globalRawMass (F.cutoff w) (primorial w) M)
                      (fun x => maskBoundedCountIntegrand gap (fun col => a (γ col)) (fun _ => C) w
                        (fun col => (model (principalTailPositions e (C.tail col)) (p col) (γ col)).val w)
                        (b w) (fun col => (C.sampleProducts hCrange x col : ℤ)))| < countTolerance)) ∧
'''
head = head.replace(needle, needle.replace('η)) ∧', 'η) ∧') + extra, 1)
proof = ''' := by
  let ε : ℝ := countTolerance / (2 * ((Fintype.card (LargeColumnSubset m) : ℝ) + 1))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hbudget : ((Fintype.card (LargeColumnSubset m) : ℝ) + 1) * ε = countTolerance / 2 := by
    have hden : (Fintype.card (LargeColumnSubset m) : ℝ) + 1 ≠ 0 := by positivity
    dsimp only [ε]
    field_simp [hden]
  obtain ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, hN⟩ :=
    selected_color_raw_counting.{u} ι r n m s hinverse cap hcap ε hε
  refine ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, ?_⟩
  intro M hM hNM gap₀ F a ha χ color
  obtain ⟨f, hf, hd, hselected⟩ := hN M hM hNM a ha χ color
  refine ⟨f, hf, hd, ?_⟩
  intro U hU
  obtain ⟨e, heM, model, hmodel, htest, hcal, hrawcal, hchains, hcommon⟩ := hselected U hU
  refine ⟨e, heM, model, hmodel, htest, hcal, hrawcal, ?_, hcommon⟩
  intro C hC
  obtain ⟨p, hp, hpivot, htail, hquality, hcorr, hreplace, hcount⟩ := hchains C hC
  refine ⟨p, hp, hpivot, htail, hquality, hcorr, hreplace, hcount, ?_⟩
  intro γ b hb
  have ht := hcount γ b hb (countTolerance/2) (by positivity)
  filter_upwards [ht] with w hw
  rw [hbudget] at hw
  linarith

end Hindman168
'''
Path('Hindman168/SelectedColorPredictionTolerance.lean').write_text(head+proof, encoding='utf-8')
print('Wrote SelectedColorPredictionTolerance; retained proof sources unchanged.')
