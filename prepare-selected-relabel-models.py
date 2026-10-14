from pathlib import Path

source = Path('Hindman168/SelectedColorAdmissibleModels.lean').read_text(encoding='utf-8')
head, _ = source.split(' := by\n', 1)
head = ('import Hindman168.SelectedColorAdmissibleModels\n'
        'import Hindman168.PrincipalBoundedCounts\n\n'
        'namespace Hindman168\nopen Filter FiniteMass MaskOriginalSampling\n'
        'open scoped BigOperators Topology Classical\nuniverse u\n\n'
        '/-- The same models have their complete bounded count on the\n'
        'actual relabeled independent harmonic coordinates. Native inverse\n'
        'existence remains an explicit unproved input. -/\n' +
        head[head.index('theorem selected_color_admissible_models'):])
head = head.replace('selected_color_admissible_models', 'selected_color_relabel_models', 1)
needle = '          (∀ C : Chain (m+1), ∀ hC : ∀ i, C.block i ⊆ energyPrincipalSet e,\n'
assert head.count(needle) == 1
extra = '''          (∀ (C : PrincipalCoordinateChain n (m+1))
            (γ : Fin (m+1) → ι) (productColor : Fin r),
            let gap := masterGapIndex M hM (energyPadding e (C.pivot 0))
            ∀ᶠ w in (U : Filter ℕ),
              |maskOriginalSubsetCorrelation gap (fun col => a (γ col)) (fun _ => C.lift e) w
                  (maskCenterAndRows gap (fun _ => C.lift e) w
                    (fun col => maskChainColorWeight m hM (C.lift e) (C.lift_range e heM)
                      (fun col => a (γ col)) χ (fun col => color (γ col)) col w))
                  (principalColorProductMask C M e (fun col => a (γ col)) χ productColor w) -
                expectation (selectedPrincipalRawMass e F w)
                  (fun x => principalBoundedCountIntegrand C M e (fun col => a (γ col)) w
                    (fun col => (model (C.tail col) (C.pivot col) (γ col)).val w)
                    (principalColorProductMask C M e (fun col => a (γ col)) χ productColor w)
                    (fun col => (C.sampleProducts x col : ℤ)))| < countTolerance) ∧
'''
head = head.replace(needle, extra+needle, 1)
proof = ''' := by
  obtain ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, hN⟩ :=
    selected_color_admissible_models.{u} ι r n m s hinverse cap hcap countTolerance hcountTolerance
  refine ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, ?_⟩
  intro M hM hNM gap₀ F a ha χ color
  obtain ⟨f, hf, hd, hselected⟩ := hN M hM hNM a ha χ color
  refine ⟨f, hf, hd, ?_⟩
  intro U hU
  obtain ⟨e, heM, hadmissible, model, hmodel, htest, hcal, hrawcal, hchains, hcommon⟩ := hselected U hU
  refine ⟨e, heM, hadmissible, model, hmodel, htest, hcal, hrawcal, ?_, hchains, hcommon⟩
  intro C γ productColor
  obtain ⟨p, hp, hpivot, htail, hquality, hcorr, hreplace, hcountslack, hcount, hproduct⟩ :=
    hchains (C.lift e) (C.lift_selected e)
  have hpEq := C.lift_pivot_coordinates e p hpivot
  subst p
  have hF := maskGeneratedMaster_conditions m gap₀ ∅ (by simp)
  have hex := (hF.principal_bounded_count_expectation e heM C
    (masterGapIndex M hM (energyPadding e (C.pivot 0))) (fun col => a (γ col))).filter_mono hU
  filter_upwards [hproduct γ productColor, hex] with w hw he
  simp only [C.lift_tail_positions] at hw
  rw [← principalColorProductMask_lift C e heM] at hw
  rw [he] at hw
  exact hw

end Hindman168
'''
Path('Hindman168/SelectedColorRelabelModels.lean').write_text(head+proof, encoding='utf-8')
print('Wrote SelectedColorRelabelModels; retained proof sources unchanged.')
