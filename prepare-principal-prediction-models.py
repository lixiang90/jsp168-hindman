from pathlib import Path

source = Path('Hindman168/SelectedColorRelabelModels.lean').read_text(encoding='utf-8')
head, _ = source.split(' := by\n', 1)
head = ('import Hindman168.SelectedColorRelabelModels\n'
        'import Hindman168.PrincipalWeightedColorCounts\n\n'
        'namespace Hindman168\nopen Filter FiniteMass MaskOriginalSampling\n'
        'open scoped BigOperators Topology Classical\nuniverse u\n\n'
        '/-- The same selected models have block calibration and complete\n'
        'weighted-versus-bounded color count on their actual selected laws.\n'
        'Native inverse existence remains explicit and unproved. -/\n' +
        head[head.index('theorem selected_color_relabel_models'):])
head = head.replace('selected_color_relabel_models', 'principal_prediction_models', 1)
needle = '          (∀ (C : PrincipalCoordinateChain n (m+1))\n'
assert head.count(needle) == 1
extra = '''          (∀ (T : Finset (Fin n)) (b : Fin n) (γ : ι),
            T.Nonempty → (∀ k ∈ T, k < b) → ∀ θ : ℝ, 0 < θ → ∀ᶠ w in (U : Filter ℕ),
            event (selectedPrincipalRawMass e F w)
              (fun x => let z : ℤ := (principalSubsetProduct (insert b T) x : ℤ)
                0 < z ∧ χ (principalBlockCoefficient M e T b (a γ) w * z.toNat) = color γ ∧
                (model T b γ).val w z ≤ 2*θ) < 3*θ + cap) ∧
          (∀ (C : PrincipalCoordinateChain n (m+1))
            (γ : Fin (m+1) → ι) (productColor : Fin r), ∀ᶠ w in (U : Filter ℕ),
            |principalWeightedColorCount C M e F (fun col => a (γ col)) χ
                (fun col => color (γ col)) productColor w -
              expectation (selectedPrincipalRawMass e F w)
                (fun x => principalBoundedCountIntegrand C M e (fun col => a (γ col)) w
                  (fun col => (model (C.tail col) (C.pivot col) (γ col)).val w)
                  (principalColorProductMask C M e (fun col => a (γ col)) χ productColor w)
                  (fun col => (C.sampleProducts x col : ℤ)))| < countTolerance) ∧
'''
head = head.replace(needle, extra+needle, 1)
proof = ''' := by
  obtain ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, hN⟩ :=
    selected_color_relabel_models.{u} ι r n m s hinverse cap hcap countTolerance hcountTolerance
  refine ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, ?_⟩
  intro M hM hNM gap₀ F a ha χ color
  obtain ⟨f, hf, hd, hselected⟩ := hN M hM hNM a ha χ color
  refine ⟨f, hf, hd, ?_⟩
  intro U hU
  obtain ⟨e, heM, hadmissible, model, hmodel, htest, hcal, hrawcal, hrelcount, hchains, hcommon⟩ := hselected U hU
  refine ⟨e, heM, hadmissible, model, hmodel, htest, hcal, hrawcal, ?_, ?_, hrelcount, hchains, hcommon⟩
  · intro T b γ hT hbefore θ hθ
    have hbefore' : ∀ y ∈ T.image (energyPrincipal e), y < energyPrincipal e b :=
      fun y hy => Finset.mem_range.mp (principalTail_before e T b hbefore hy)
    have hF := maskGeneratedMaster_conditions m gap₀ ∅ (by simp)
    have hex := (hF.principal_block_product_event e heM T b hT hbefore).filter_mono hU
    filter_upwards [hcal T b γ (hT.image _) hbefore' θ hθ, hex] with w hw he
    let E : ℤ → Prop := fun y => 0 < y ∧
      χ (principalBlockCoefficient M e T b (a γ) w * y.toNat) = color γ ∧
      (model T b γ).val w y ≤ 2*θ
    have hw' : event (originalBlockProductMass F (T.image (energyPrincipal e))
        (energyPrincipal e b) (hT.image _) (principalTail_before e T b hbefore) w) E <
        3*θ + cap := by
      dsimp only [E]
      rw [principalBlockCoefficient_lift e heM]
      exact hw
    exact (he E).trans_lt hw'
  · intro C γ productColor
    have hex := (mask_principal_weighted_count_exact C e heM hM
      (masterGapIndex M hM (energyPadding e (C.pivot 0))) (fun col => a (γ col))
      (fun col => ha (γ col)) χ (fun col => color (γ col)) productColor).filter_mono hU
    filter_upwards [hrelcount C γ productColor, hex] with w hw he
    rw [he] at hw
    exact hw

end Hindman168
'''
Path('Hindman168/PrincipalPredictionModels.lean').write_text(head+proof, encoding='utf-8')
print('Wrote PrincipalPredictionModels; retained proof sources unchanged.')
