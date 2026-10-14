import Hindman168.PositivePrincipalSumConclusion
import Hindman168.PositivePrincipalSumTolerances
import Hindman168.PositivePrincipalSumRatios

/-!
# Tolerances-first final deduction from the two paper principles

For fixed finite scale lists and the alignment mass lower bound, choose
the threshold and prediction tolerance *before* parameters and models.
Every exact prediction output whose original adding-pair event satisfies
the ordinary liminf bound then yields an exact finite FS/FP witness.

This proves the final Section 2.5 deduction. It does not prove existence
of the native inverse input or the global alignment mass bound.
-/

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

/-- The numerical choices depend only on the pre-model finite catalogues
and positive alignment mass, as required by the paper's quantifier order. -/
theorem principal_final_deduction_tolerances
    (n m r : ℕ) (B : Finset (Fin n → ℚ)) (A : Finset ℚ)
    (hclosed : FiniteScaleClosure B A) (δ : ℝ) (hδ : 0 < δ) :
    ∃ θ η : ℝ, 0 < θ ∧ θ < 1/4 ∧ 0 < η ∧
      ∀ (d M : ℕ) (P : Finset (MvPolynomial (Fin d) ℤ)) (F : MasterParameterFamily),
      MasterParameterConditions M A P F →
      (∀ χ : ℕ → Fin r, ∀ x : Fin n → ℕ,
        ∃ C : PrincipalCoordinateChain n (m+1), ∃ κ : Fin r,
          ∀ J : Finset (Fin (m+1)), J.Nonempty → χ (∏ i ∈ J, C.sampleProducts x i) = κ) →
      ∀ (e : Fin (2*n) ↪o ℕ), (∀ j, e j < M) →
      ∀ (U : Ultrafilter ℕ), (U : Filter ℕ) ≤ atTop →
      ∀ (χ : ℕ → Fin r)
        (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ),
      PrincipalPredictionLimitData (m := m) M e F U η η
        (scaleColorFactor A r) χ (scaleColorValue A r) S →
      (∀ T b γ w y, S T b γ w y ∈ Set.Icc (0 : ℝ) 1) →
      δ ≤ Filter.liminf (fun w => event (selectedPrincipalRawMass e F w)
        (PrincipalSumAlignmentEvent M e B A hclosed S θ w)) atTop →
      ∃ W : Finset ℕ, W.card = m+1 ∧ (∀ x ∈ W, 0 < x) ∧ MonoFSFP χ W := by
  obtain ⟨θ, η, hθ, hθsmall, hη, hbudget⟩ := positivePrincipalSum_choose_tolerances
    (Fintype.card (PrincipalSumCalibrationIndex n A r))
    (Fintype.card (PrincipalSumCountIndex m B r))
    (Fintype.card (NonemptyColumnSubset (m+1))) (δ/2) (by linarith)
  refine ⟨θ, η, hθ, hθsmall, hη, ?_⟩
  intro d M P F hF hselect e heM U hU χ S hdata hS hliminf
  have hmass := positivePrincipalSum_alignment_liminf (selectedPrincipalRawMass e F)
    (PrincipalSumAlignmentEvent M e B A hclosed S θ)
    ((hF.selected_principal_raw_probability e heM).mono (fun _ h => h.1))
    δ hδ hliminf U hU
  exact principal_prediction_alignment_finite_witness hF hselect e heM B hclosed U hU
    η η χ S hdata hS θ (δ/2) hθ (by linarith) hmass hbudget

end Hindman168
