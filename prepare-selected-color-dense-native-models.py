from pathlib import Path

source = Path('Hindman168/SelectedNativeMaskCorrelation.lean').read_text(encoding='utf-8')
head, _ = source.split(' := by\n', 1)
start = head.index('/-- One family')
head = ('import Hindman168.MaskColorFamilySelectedQuality\n'
        'import Hindman168.MaskColorNativePredictionTransfer\n'
        'import Hindman168.SelectedNativeMaskCorrelation\n\n'
        'namespace Hindman168\nopen Filter FiniteMass MaskOriginalSampling\n'
        'open scoped BigOperators Topology Classical\nuniverse u\n\n' + head[start:])
head = head.replace('selected_native_mask_original_correlations', 'selected_color_dense_native_models', 1)
head = head.replace('(n m s : ℕ)', '(r n m s : ℕ)', 1)
left = head.index('      ∀ (U : Ultrafilter ℕ)')
right = head.index('      ∃ e : Fin (2 * n)', left)
head = head[:left] + '''      ∀ (a : ι → ℚ) (_ha : ∀ γ, 0 < a γ)
        (χ : ℕ → Fin r) (color : ι → Fin r),
      ∃ f : Finset ℕ → (i : ℕ) → ι →
        boundedHilbertFamilies (fun w => FiniteMassL2 (originalPivotMass F i w)),
        (∀ T i γ w y, 0 ≤ (f T i γ).val w y ∧ (f T i γ).val w y ≤ 1) ∧
        (∀ T : Finset ℕ, ∀ i : Fin M, ∀ hT : T.Nonempty,
          ∀ hTi : T ⊆ Finset.range i.val, ∀ γ : ι,
          MaskColorBlockDualControl m (s+1) hM T i hT hTi (a γ) χ (color γ)
            (fun w y => (f T i.val γ).val w y)) ∧
      ∀ (U : Ultrafilter ℕ) (_hU : (U : Filter ℕ) ≤ atTop),
''' + head[right:]
old = '(∀ j, e j < M) ∧'
assert head.count(old) == 1
head = head.replace(old, '∃ heM : ∀ j, e j < M,', 1)
needle = '              ∀ (a : Fin (m+1) → ℚ)'
assert head.count(needle) == 1
quality = '''              let hCrange : ∀ col, C.block col ⊆ Finset.range M := fun col y hy => by
                obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp (hC col hy)
                exact Finset.mem_range.mpr (heM _)
              (∀ γ : Fin (m+1) → ι, ∀ η : ℝ, 0 < η → ∀ᶠ w in (U : Filter ℕ),
                maskModelReplacementQuality gap (fun col => a (γ col)) (fun _ => C)
                  (maskChainColorWeight m hM C hCrange (fun col => a (γ col)) χ
                    (fun col => color (γ col)))
                  (fun col w y => (f (C.tail col) (C.pivot col) (γ col)).val w y) η w) ∧
'''
head = head.replace(needle, quality + needle, 1)
head = head.replace('(∀ C : Chain (m+1), (∀ i, C.block i ⊆ energyPrincipalSet e) →',
                    '(∀ C : Chain (m+1), ∀ hC : ∀ i, C.block i ⊆ energyPrincipalSet e,', 1)
head = head.replace('              ∀ (a : Fin (m+1) → ℚ)', '              (∀ (a : Fin (m+1) → ℚ)', 1)
needle = '|maskOriginalSubsetCorrelation gap a (fun _ => C) w (H w) (b w)| ≤ ε) ∧\n          ∃ G'
assert head.count(needle) == 1
full = '''|maskOriginalSubsetCorrelation gap a (fun _ => C) w (H w) (b w)| ≤ ε) ∧
              (∀ (γ : Fin (m+1) → ι)
                (H : ℕ → NonemptyColumnSubset (m+1) → ℤ → ℝ)
                (b : ℕ → Finset (Fin (m+1)) → ℤ → ℝ),
                (∀ᶠ w in (U : Filter ℕ), maskOriginalSubsetAdmissible gap (fun _ => C) w (H w) (b w)) →
                (∀ᶠ w in (U : Filter ℕ), ∀ V : NonemptyColumnSubset (m+1), 2 ≤ V.val.card →
                  H w V = maskChainColorWeight m hM C hCrange (fun col => a (γ col)) χ
                    (fun col => color (γ col)) (V.val.max' V.property) w) →
                ∀ᶠ w in (U : Filter ℕ),
                  |maskOriginalSubsetCorrelation gap (fun col => a (γ col)) (fun _ => C) w (H w) (b w) -
                    maskOriginalSubsetCorrelation gap (fun col => a (γ col)) (fun _ => C) w
                      (maskSubsetModelReplacement (H w) (fun col y =>
                        (model (principalTailPositions e (C.tail col)) (p col) (γ col)).val w y)) (b w)| ≤
                    ((Fintype.card (LargeColumnSubset m) : ℝ) + 1) * ε)) ∧
          ∃ G'''
head = head.replace(needle, full, 1)
body = ''' := by
  obtain ⟨J, hJ, κ, τ, hκ, hτ, hsmall, N, hN⟩ :=
    selected_native_mask_original_correlations.{u} ι n m s hinverse ε hε
  refine ⟨J, hJ, κ, τ, hκ, hτ, hsmall, N, ?_⟩
  intro M hM hNM gap₀ F a ha χ color
  obtain ⟨f, hf, hd⟩ := mask_color_block_hilbert_family ι m (s+1) (by omega) hM a ha χ color
  refine ⟨f, hf, hd, ?_⟩
  intro U hU
  obtain ⟨e, heM, model, hmodel, hchains, hcommon⟩ := hN M hM hNM U hU f hf
  refine ⟨e, heM, model, hmodel, ?_, hcommon⟩
  intro C hC
  obtain ⟨p, hpmono, hp, hbefore, hFS⟩ := hchains C hC
  refine ⟨p, hpmono, hp, hbefore, ?_, hFS, ?_⟩
  · intro γ η hη
    exact hU (mask_color_family_selected_chain_quality ι m (s+1) hM a ha χ color f hf hd
      e heM C hC p hp γ η hη)
  · intro γ H b hH htarget
    let gap := masterGapIndex M hM (energyPadding e (p 0))
    have hCrange : ∀ col, C.block col ⊆ Finset.range M := by
      intro col y hy
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp (hC col hy)
      exact Finset.mem_range.mpr (heM _)
    exact mask_color_native_prediction_transfer gap (fun col => a (γ col)) (fun _ => C)
      (fun _ => hCrange) U hU
      (maskChainColorWeight m hM C hCrange (fun col => a (γ col)) χ (fun col => color (γ col)))
      (fun col w y => (f (C.tail col) (C.pivot col) (γ col)).val w y)
      (fun col w y => (model (principalTailPositions e (C.tail col)) (p col) (γ col)).val w y)
      (fun col => hf _ _ _) (fun col => (hmodel _ _ _).2.1) ε hε
      (hU (mask_color_family_selected_chain_quality ι m (s+1) hM a ha χ color f hf hd
        e heM C hC p hp γ ε hε))
      (fun z H b hH ht => hFS (fun col => a (γ col)) (fun col => ha (γ col)) z
        (γ (targetRootAnchor gap z)) H b hH ht) H b hH htarget

end Hindman168
'''
head = head.replace('/-- One family of actual selected native models controls F-S in every\n'
                    'original subset correlation on every selected chain. The quotient scale,\n'
                    'accuracies and required master count are chosen first. The interval\n'
                    'inverse existence inputs remain explicit hypotheses. -/',
                    '/-- Actual coloring dense models are chosen before the ultrafilter and\n'
                    'selected indices. The same family supplies every later rho-F replacement\n'
                    'and every selected native F-S estimate, preserving coarse representation,\n'
                    'projection accuracy and one common native manifold. The inverse\n'
                    'existence hypotheses remain explicit and unproved. -/')
Path('Hindman168/SelectedColorDenseNativeModels.lean').write_text(head + body, encoding='utf-8')
print('Wrote the complete selected coloring dense/native model assembly.')
