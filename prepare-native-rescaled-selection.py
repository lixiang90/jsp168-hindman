from pathlib import Path
source = Path('Hindman168/RoughNativeLabelledPieceTests.lean').read_text(encoding='utf-8')
start = source.index('theorem rough_native_labelled_piece_tests')
end = source.index('\n        ∀ x ∈', start)
header = source[start:end].replace('rough_native_labelled_piece_tests', 'rough_native_rescaled_piece_selection', 1).replace('∃ hN : 0 < N', '∃ _ : 0 < N')
conclusion = '''
        ∀ (a0 : κ → ℤ) (t : ℕ), 0 < t → t.Coprime K →
          ∀ (c θ η : ℝ), 0 < c → 2*(t : ℝ) ≤ c*Z →
          (∀ j, c*Z ≤ (r j : ℝ)-l j) →
          θ+B*(((N ^ Fintype.card κ*K ^ Fintype.card κ : ℕ) : ℝ)*
            Fintype.card κ*(5*(t : ℝ)/(c*Z)))+2*(εfreeze+εapprox) < η →
          η ≤ |FiniteMass.expectation (FiniteMass.uniformFinsetMass (alignmentBoxClass l r a0 t))
              (fun x => F (QuotientGroup.mk (P (Option.elim · (z : ℝ) (fun j => (x j : ℝ))))))-
            FiniteMass.expectation (FiniteMass.uniformFinsetMass
              (Fintype.piFinset (fun j => Finset.Ico (l j) (r j))))
              (fun x => F (QuotientGroup.mk (P (Option.elim · (z : ℝ) (fun j => (x j : ℝ))))))| →
          ∃ (p : (κ → Fin N) × (κ → Fin K)) (v : κ → ℤ),
            let u : κ → ℤ := fun j => (p.2 j).val
            let lo := roughResidueBoxEndpoint (roughBoxLower l r N p.1) u K
            let hi := roughResidueBoxEndpoint (roughBoxUpper l r N p.1) u K
            0 < (alignmentBoxClass lo hi v t).card ∧
            0 < (Fintype.piFinset (fun j => Finset.Ico (lo j) (hi j))).card ∧
            θ < |FiniteMass.expectation (FiniteMass.uniformFinsetMass (alignmentBoxClass lo hi v t))
                (fun y => tests p (QuotientGroup.mk (Q (indices p)
                  (Option.elim · (z : ℝ) (fun j => (roughResidueBoxAffine u K y j : ℝ))))))-
              FiniteMass.expectation (FiniteMass.uniformFinsetMass
                (Fintype.piFinset (fun j => Finset.Ico (lo j) (hi j))))
                (fun y => tests p (QuotientGroup.mk (Q (indices p)
                  (Option.elim · (z : ℝ) (fun j => (roughResidueBoxAffine u K y j : ℝ))))))| := by
  intro family
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ j, MetricSpace ((family j).G ⧸ (family j).Γ) := fun j => (family j).metric
  letI : ∀ j, TopologicalSpace ((family j).G ⧸ (family j).Γ) := fun j =>
    (family j).metric.toUniformSpace.toTopologicalSpace
  obtain ⟨N, L, hN, hstage⟩ := rough_native_labelled_piece_tests D S hS χ hχ hQ V hVr hVS hχV
    K hK hperiod support d hd A C B hA hC hB Lip hεf hεa
  refine ⟨N, L, hN, ?_⟩
  intro w H q z Z P0 theta M0 M hmodels hz hZ h0 hconst l r hlen hside hl hr F hF hbound m a P hP hchar Q
  obtain ⟨indices, tests, hlip, hsup, herr⟩ := hstage w H q z Z P0 theta M0 M
    hmodels hz hZ h0 hconst l r hlen hside hl hr F hF hbound P hP hchar
  refine ⟨indices, tests, hlip, hsup, ?_⟩
  intro a0 t ht hcop c θ η hc htZ hlen' hgap hbad
  exact rough_dependent_rescaled_selection l r a0 N K t hN hK ht hcop c Z hc hZ htZ hlen'
    (fun p => (family (indices p)).G ⧸ (family (indices p)).Γ) tests
    (fun p x => QuotientGroup.mk (Q (indices p) (Option.elim · (z : ℝ) (fun j => (x j : ℝ)))))
    (fun x => F (QuotientGroup.mk (P (Option.elim · (z : ℝ) (fun j => (x j : ℝ))))))
    θ B η (εfreeze+εapprox) hB hsup herr hgap hbad

end Hindman168
'''
prefix = '''import Hindman168.RoughNativeLabelledPieceTests
import Hindman168.RoughDependentRescaledSelection

namespace Hindman168
open MvPolynomial
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

'''
Path('Hindman168/RoughNativeRescaledPieceSelection.lean').write_text(prefix+header+conclusion, encoding='utf-8')
