from pathlib import Path

source = Path('Hindman168/SelectedColorGlobalCalibration.lean').read_text(encoding='utf-8')
head, _ = source.split(' := by\n', 1)
head = ('import Hindman168.SelectedColorGlobalCalibration\n'
        'import Hindman168.MaskBoundedCountSampling\n\n'
        'namespace Hindman168\nopen Filter FiniteMass MaskOriginalSampling\n'
        'open scoped BigOperators Topology Classical\nuniverse u\n\n'
        '/-- The same selected models give the original full raw-coordinate count\n'
        'comparison, retaining every product mask and original center weight.\n'
        'Calibration and all earlier selected model properties are retained.\n'
        'Native inverse existence is still an explicit unproved hypothesis. -/\n' +
        head[head.index('theorem selected_color_global_calibration'):])
head = head.replace('selected_color_global_calibration', 'selected_color_raw_counting', 1)
needle = '                    ((Fintype.card (LargeColumnSubset m) : ℝ) + 1) * ε)) ∧\n'
assert head.count(needle) == 1
count = '''              (∀ (γ : Fin (m+1) → ι)
                (b : ℕ → Finset (Fin (m+1)) → ℤ → ℝ),
                (∀ᶠ w in (U : Filter ℕ),
                  ∀ V ∈ (Finset.univ : Finset (Fin (m+1))).powerset.erase ∅,
                    ∀ y, |b w V y| ≤ 1) →
                ∀ η : ℝ, 0 < η → ∀ᶠ w in (U : Filter ℕ),
                  |maskOriginalSubsetCorrelation gap (fun col => a (γ col)) (fun _ => C) w
                    (maskCenterAndRows gap (fun _ => C) w
                      (fun col => maskChainColorWeight m hM C hCrange
                        (fun col => a (γ col)) χ (fun col => color (γ col)) col w)) (b w) -
                    expectation (globalRawMass (F.cutoff w) (primorial w) M)
                      (fun x => maskBoundedCountIntegrand gap (fun col => a (γ col)) (fun _ => C) w
                        (fun col => (model (principalTailPositions e (C.tail col)) (p col) (γ col)).val w)
                        (b w) (fun col => (C.sampleProducts hCrange x col : ℤ)))| <
                    ((Fintype.card (LargeColumnSubset m) : ℝ) + 1) * ε + η)) ∧
'''
head = head.replace(needle, needle.replace('ε)) ∧', 'ε) ∧') + count, 1)
proof = ''' := by
  obtain ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, hN⟩ :=
    selected_color_global_calibration.{u} ι r n m s hinverse cap hcap ε hε
  refine ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, ?_⟩
  intro M hM hNM gap₀ F a ha χ color
  obtain ⟨f, hf, hd, hselected⟩ := hN M hM hNM a ha χ color
  refine ⟨f, hf, hd, ?_⟩
  intro U hU
  obtain ⟨e, heM, model, hmodel, htest, hcal, hrawcal, hchains, hcommon⟩ := hselected U hU
  refine ⟨e, heM, model, hmodel, htest, hcal, hrawcal, ?_, hcommon⟩
  intro C hC
  obtain ⟨p, hp, hpivot, htail, hquality, hcorr, hreplace⟩ := hchains C hC
  refine ⟨p, hp, hpivot, htail, hquality, hcorr, hreplace, ?_⟩
  intro γ b hb η hη
  let gap := masterGapIndex M hM (energyPadding e (p 0))
  have hCrange : ∀ col, C.block col ⊆ Finset.range M := fun col y hy => by
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp (hC col hy)
    exact Finset.mem_range.mpr (heM _)
  let ρ := maskChainColorWeight m hM C hCrange
    (fun col => a (γ col)) χ (fun col => color (γ col))
  let S (col : Fin (m+1)) := (model (principalTailPositions e (C.tail col)) (p col) (γ col)).val
  let H (w : ℕ) := maskCenterAndRows gap (fun _ => C) w (fun col => ρ col w)
  have hρ := hU (maskChainColorWeight_bounds m hM C hCrange gap
    (fun col => a (γ col)) χ (fun col => color (γ col)))
  have hν := hU (maskSubsetTailMask_eventually_nonneg gap (fun _ => C) (fun _ => hCrange))
  have hH : ∀ᶠ w in (U : Filter ℕ), maskOriginalSubsetAdmissible gap (fun _ => C) w (H w) (b w) := by
    filter_upwards [hρ, hν, hb] with w hr hn hbw
    exact maskCenterAndRows_admissible gap (fun _ => C) w (fun col => ρ col w) (b w) hn hr hbw
  have hr := hreplace γ H b hH (Eventually.of_forall (fun w V hV => by
    simp only [H, maskCenterAndRows, if_pos hV]
    rfl))
  have hr' : ∀ᶠ w in (U : Filter ℕ),
      |maskOriginalSubsetCorrelation gap (fun col => a (γ col)) (fun _ => C) w (H w) (b w) -
        maskOriginalSubsetCorrelation gap (fun col => a (γ col)) (fun _ => C) w
          (maskCenterAndRows gap (fun _ => C) w (fun col => S col w)) (b w)| ≤
        ((Fintype.card (LargeColumnSubset m) : ℝ) + 1) * ε := by
    filter_upwards [hr] with w hw
    simpa only [H, maskCenterAndRows_replacement] using hw
  exact mask_original_count_sampling_transfer gap (fun col => a (γ col))
    (fun col => ha (γ col)) (fun _ => C) (fun _ => hCrange) U hU ρ S
    (fun col => (hmodel _ _ _).2.1) b hb _ hr' η hη

end Hindman168
'''
Path('Hindman168/SelectedColorRawCounting.lean').write_text(head+proof, encoding='utf-8')
print('Wrote SelectedColorRawCounting; retained proof sources unchanged.')
