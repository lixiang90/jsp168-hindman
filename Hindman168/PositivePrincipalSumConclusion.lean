import Hindman168.PositivePrincipalSumEvents
import Hindman168.PositivePrincipalSumLimits
import Hindman168.PrincipalCountWitness

/-!
# The final counting deduction from prediction and adding-pair alignment

Prediction is used through its existing exact limit-data structure.
Alignment is used through the original simultaneous adding-pair event.
The event-to-model selection is proved, not assumed as a model-count or
actual-count positivity hypothesis. Proving positive alignment-event mass
uniformly over native models remains the analytic Principle 2.4 task.
-/

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

/-- From the original prediction limits and positive alignment-event mass,
all actual counts have a positive finite sum at late ultrafilter stages. -/
theorem principal_prediction_alignment_positive_sum
    {d n m M r : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A P F)
    (hselect : ∀ χ : ℕ → Fin r, ∀ x : Fin n → ℕ,
      ∃ C : PrincipalCoordinateChain n (m+1), ∃ κ : Fin r,
        ∀ J : Finset (Fin (m+1)), J.Nonempty → χ (∏ i ∈ J, C.sampleProducts x i) = κ)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (B : Finset (Fin n → ℚ)) (hclosed : FiniteScaleClosure B A)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (cap η : ℝ) (χ : ℕ → Fin r)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (hdata : PrincipalPredictionLimitData (m := m) M e F U cap η
      (scaleColorFactor A r) χ (scaleColorValue A r) S)
    (hS : ∀ T b γ w y, S T b γ w y ∈ Set.Icc (0 : ℝ) 1)
    (θ δ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (halignmass : ∀ᶠ w in (U : Filter ℕ), δ ≤ event (selectedPrincipalRawMass e F w)
      (PrincipalSumAlignmentEvent M e B A hclosed S θ w))
    (hbudget : 0 < θ ^ Fintype.card (NonemptyColumnSubset (m+1)) *
      (δ - (Fintype.card (PrincipalSumCalibrationIndex n A r) : ℝ) * (3*θ + cap)) -
      (Fintype.card (PrincipalSumCountIndex m B r) : ℝ) * η) :
    ∀ᶠ w in (U : Filter ℕ), 0 < ∑ q : PrincipalSumCountIndex m B r,
      principalWeightedColorCount q.2.1 M e F
        (fun i => finiteScaleBlockProduct q.1.val (q.2.1.block i)) χ
        (fun _ => q.2.2) q.2.2 w := by
  have hμ : ∀ᶠ w in (U : Filter ℕ), ∀ x, 0 ≤ selectedPrincipalRawMass e F w x :=
    ((hF.selected_principal_raw_probability e heM).mono (fun _ h => h.1)).filter_mono hU
  have hcoef := (hF.principal_individual_coefficients_eventually e heM).filter_mono hU
  have hpoint : ∀ᶠ w in (U : Filter ℕ), ∀ x ∈ (selectedPrincipalRawMass e F w).support,
      PrincipalSumAlignmentEvent M e B A hclosed S θ w x →
      (∀ j : PrincipalSumCalibrationIndex n A r,
        ¬ (let z : ℤ := (principalSubsetProduct (insert j.1.val.2 j.1.val.1) x : ℤ)
          0 < z ∧ χ (principalBlockCoefficient M e j.1.val.1 j.1.val.2
            (scaleColorFactor A r j.2) w * z.toNat) = scaleColorValue A r j.2 ∧
            S j.1.val.1 j.1.val.2 j.2 w z ≤ 2*θ)) →
      ∃ q : PrincipalSumCountIndex m B r,
        θ ^ Fintype.card (NonemptyColumnSubset (m+1)) ≤
          principalBoundedCountIntegrand q.2.1 M e
            (fun i => scaleColorFactor A r (principalSumGamma B A hclosed q i)) w
            (fun i => S (q.2.1.tail i) (q.2.1.pivot i) (principalSumGamma B A hclosed q i) w)
            (principalColorProductMask q.2.1 M e
              (fun i => scaleColorFactor A r (principalSumGamma B A hclosed q i)) χ q.2.2 w)
            (fun i => (q.2.1.sampleProducts x i : ℤ)) := by
    filter_upwards [hcoef] with w hw
    intro x hx halign hgood
    apply principal_alignment_good_sample_selects_model hselect e heM B A hclosed χ S θ
      hθ.le hθ1 w x (fun i => hF.principal_raw_support_positive e w x hx i) ?_ halign hgood
    intro b k
    apply hw b.val ?_ k
    intro j
    have hh := hclosed b.val b.property {j} (by simp)
    simpa only [finiteScaleBlockProduct, Finset.prod_singleton] using hh
  have h := principal_prediction_positive_sum_of_alignment_selection M e F U cap η
    (scaleColorFactor A r) χ (scaleColorValue A r) S hdata hS hμ
    (fun j : PrincipalSumCalibrationIndex n A r => j.1.val.1)
    (fun j => j.1.val.2) (fun j => j.2)
    (fun j => j.1.property.1) (fun j => j.1.property.2)
    (fun q : PrincipalSumCountIndex m B r => q.2.1)
    (principalSumGamma B A hclosed) (fun q => q.2.2)
    (PrincipalSumAlignmentEvent M e B A hclosed S θ)
    θ δ (θ ^ Fintype.card (NonemptyColumnSubset (m+1))) hθ (pow_nonneg hθ.le _)
    halignmass hpoint hbudget
  simpa only [principalSumGamma, scaleBlockColorIndex, scaleColorFactor, scaleColorValue,
    finiteScaleBlockProduct] using h

/-- The complete final deduction to an exact finite FS/FP witness.
The remaining inputs are prediction and original alignment-event mass,
not any assertion of positive actual or model counts. -/
theorem principal_prediction_alignment_finite_witness
    {d n m M r : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A P F)
    (hselect : ∀ χ : ℕ → Fin r, ∀ x : Fin n → ℕ,
      ∃ C : PrincipalCoordinateChain n (m+1), ∃ κ : Fin r,
        ∀ J : Finset (Fin (m+1)), J.Nonempty → χ (∏ i ∈ J, C.sampleProducts x i) = κ)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (B : Finset (Fin n → ℚ)) (hclosed : FiniteScaleClosure B A)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (cap η : ℝ) (χ : ℕ → Fin r)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (hdata : PrincipalPredictionLimitData (m := m) M e F U cap η
      (scaleColorFactor A r) χ (scaleColorValue A r) S)
    (hS : ∀ T b γ w y, S T b γ w y ∈ Set.Icc (0 : ℝ) 1)
    (θ δ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (halignmass : ∀ᶠ w in (U : Filter ℕ), δ ≤ event (selectedPrincipalRawMass e F w)
      (PrincipalSumAlignmentEvent M e B A hclosed S θ w))
    (hbudget : 0 < θ ^ Fintype.card (NonemptyColumnSubset (m+1)) *
      (δ - (Fintype.card (PrincipalSumCalibrationIndex n A r) : ℝ) * (3*θ + cap)) -
      (Fintype.card (PrincipalSumCountIndex m B r) : ℝ) * η) :
    ∃ W : Finset ℕ, W.card = m+1 ∧ (∀ x ∈ W, 0 < x) ∧ MonoFSFP χ W := by
  have hp := principal_prediction_alignment_positive_sum hF hselect e heM B hclosed U hU
    cap η χ S hdata hS θ δ hθ hθ1 halignmass hbudget
  apply hF.principal_positive_sum_yields_finite_witness e heM
    (fun q : PrincipalSumCountIndex m B r => q.2.1)
    (fun q i => finiteScaleBlockProduct q.1.val (q.2.1.block i)) ?_ χ (fun q => q.2.2)
    (hp.frequently.filter_mono hU)
  intro q i
  exact hclosed q.1.val q.1.property (q.2.1.block i) (by simp [PrincipalCoordinateChain.block])

end Hindman168
