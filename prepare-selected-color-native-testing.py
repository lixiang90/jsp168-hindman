from pathlib import Path

source = Path('Hindman168/SelectedColorDenseNativeModels.lean').read_text(encoding='utf-8')
head, _ = source.split(' := by\n', 1)
start = head.index('theorem selected_color_dense_native_models')
head = ('import Hindman168.SelectedColorBlockCoarseTesting\n\n'
        'namespace Hindman168\nopen Filter FiniteMass MaskOriginalSampling\n'
        'open scoped BigOperators Topology Classical\nuniverse u\n\n'
        '/-- The same selected models satisfy both original subset-count\n'
        'replacement and coarse native testing. Inverse existence remains\n'
        'an explicit hypothesis, and the native test is fixed before the stage. -/\n'
        + head[start:])
head = head.replace('selected_color_dense_native_models', 'selected_color_native_testing_models', 1)
needle = '          (∀ C : Chain (m+1),'
assert head.count(needle) == 1
test = '''          (∀ (T : Finset (Fin n)) (b : Fin n) (γ : ι),
            ∀ hT : (T.image (energyPrincipal e)).Nonempty,
            ∀ hbefore : ∀ y ∈ T.image (energyPrincipal e), y < energyPrincipal e b,
            ∀ v : ℕ → ℤ → ℝ,
              NativePieceRepresented.{u} s F (masterGapIndex M hM (energyPadding e b)) v →
              (∀ w y, |v w y| ≤ 1) → ∀ η : ℝ, 0 < η → ∀ᶠ w in (U : Filter ℕ),
              |expectation (originalPivotMass F (energyPrincipal e b) w)
                (fun y => (maskBlockColorWeight m hM (T.image (energyPrincipal e))
                  ⟨energyPrincipal e b, heM _⟩ hT
                  (fun y hy => Finset.mem_range.mpr (hbefore y hy))
                  (a γ) χ (color γ) w y - (model T b γ).val w y) * v w y)| < τ + η) ∧
'''
head = head.replace(needle, test + needle, 1)
body = ''' := by
  obtain ⟨J, hJ, κ, τ, hκ, hτ, hsmall, N, hN⟩ :=
    selected_color_dense_native_models.{u} ι r n m s hinverse ε hε
  refine ⟨J, hJ, κ, τ, hκ, hτ, hsmall, N, ?_⟩
  intro M hM hNM gap₀ F a ha χ color
  obtain ⟨f, hf, hd, hselected⟩ := hN M hM hNM a ha χ color
  refine ⟨f, hf, hd, ?_⟩
  intro U hU
  obtain ⟨e, heM, model, hmodel, hchains, hcommon⟩ := hselected U hU
  refine ⟨e, heM, model, hmodel, ?_, hchains, hcommon⟩
  intro T b γ hT hbefore v hv hb η hη
  exact selected_color_block_coarse_testing ι m s hM a χ color f hf hd U hU e heM
    T b γ hT hbefore (model T b γ) τ (hmodel T b γ).2.2 v hv hb η hη

end Hindman168
'''
Path('Hindman168/SelectedColorNativeTestingModels.lean').write_text(head + body, encoding='utf-8')
print('Wrote SelectedColorNativeTestingModels.lean; retained source unchanged.')
