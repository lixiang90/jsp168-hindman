import Hindman168.SelectedAlignmentRouteHarmonicCoverage

/-! Exact original-kernel extension, uniform over every outside event.
The multiplier depends only on the fixed finite route plan. All local
cover and exposure exception inputs have already been proved. -/
namespace Hindman168
open Filter FiniteMass
open scoped Classical Topology ENNReal NNReal BigOperators
attribute [local instance] alignmentAddingPairFintype

theorem selected_alignment_route_pivot_extension
    {d n M : ℕ} {κ : Type*} {A : Finset ℚ} {Poly : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A Poly F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n) (q₀ : ℕ) (hq : 0 < q₀)
    (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ) (θ : ℝ)
    (plan : List (AlignmentPivotStage n i)) (incoming : Finset (Fin n → ℚ))
    (b : Fin n → ℚ) (hb : b ∈ incoming)
    (requests : List (AlignmentPivotRequest n i)) (hQ : 0 < (principalPivotRoutes plan).card)
    (hfailure : Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) M)
      (fun x => selectedAlignmentRawRouteCellMass F e heM i q₀ w x S θ plan b requests <
        ((3 / (4 * ((principalPivotRoutes plan).card : ℝ≥0)) : ℝ≥0) : ℝ≥0∞))) atTop (𝓝 0)) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧ ∀ᶠ w in atTop,
      ∀ E : ({j : Fin M // j ≠ principalAlignmentEmbedding e heM i} → ℕ) → Prop,
      (1 / (3 * ((principalPivotRoutes plan).card : ℝ)^2)) *
        event (selectedAlignmentOutsideRawMass F w (principalAlignmentEmbedding e heM i)) E - err w ≤
      event (conditionalJoint (selectedAlignmentOutsideRawMass F w (principalAlignmentEmbedding e heM i))
        (fun _ => integerMass (F.cutoff w (energyPrincipal e i)) (primorial w)))
        (fun xp => E xp.1 ∧ selectedAlignmentSignedRouteSecured (principalAlignmentEmbedding e heM) i F q₀ w
          (insertPivotCoordinate (principalAlignmentEmbedding e heM i) xp.1 0) S θ plan b requests xp.2) := by
  classical
  let pivot := principalAlignmentEmbedding e heM i
  let V := principalPivotRoutes plan
  letI : Nonempty V := by
    obtain ⟨route,hr⟩ := Finset.card_pos.mp hQ
    exact ⟨⟨route,hr⟩⟩
  let μ := fun w => selectedAlignmentOutsideRawMass F w pivot
  let expose := fun w (_x : {j : Fin M // j ≠ pivot} → ℕ) =>
    principalMicrocellExposure (selectedPrincipalMicrocellWidth F e w i) (F.modulus w)
  let good := fun w => selectedAlignmentFineRouteGood F e heM i q₀ w S θ plan b requests
  let P := fun w x z => selectedAlignmentSignedRouteSecured (principalAlignmentEmbedding e heM) i F q₀ w
    (insertPivotCoordinate pivot x 0) S θ plan b requests z
  let shift := fun (route : V) w x => selectedAlignmentOutsideRouteShift
    (principalAlignmentEmbedding e heM) i F q₀ w plan b route.val x
  let C := selectedAlignmentRouteShiftBudget (principalAlignmentEmbedding e heM) q₀ plan incoming
  have hs : ∀ᶠ w in atTop, ∀ route : V, ∀ x, x ∈ (μ w).support →
      (primorial w : ℤ) ∣ shift route w x ∧
      |(shift route w x : ℝ)| ≤ (C : ℝ) * (F.auxiliary w pivot.val : ℝ)^2 := by
    filter_upwards [eventually_ge_atTop (q₀+1)] with w hw
    intro route x _hx
    refine ⟨selected_alignment_route_shift_divisible F (principalAlignmentEmbedding e heM) hq hw
      plan b route.val (insertPivotCoordinate pivot x 0), ?_⟩
    exact_mod_cast selected_alignment_route_shift_auxiliary_bound hF (principalAlignmentEmbedding e heM)
      q₀ w plan incoming b hb route.val route.property (insertPivotCoordinate pivot x 0)
  obtain ⟨err,he,hh⟩ := principal_master_exposed_pivot_extension hF pivot μ expose good P shift
    (C : ℝ) 2 V.card (Nat.cast_nonneg _) hQ
    (selected_alignment_outside_raw_geometry hF pivot) hs
    (by filter_upwards [selected_alignment_good_fine_harmonic_cover hF e heM i q₀ S θ plan b requests hQ]
        with w hw x _hx t ht hg
        exact hw x t ht hg)
    (selected_alignment_fine_route_failure_tendsto hF e heM i q₀ S θ plan b requests hfailure)
  refine ⟨err,he,?_⟩
  have hpivot : (principalAlignmentEmbedding e heM i).val = energyPrincipal e i := rfl
  simpa only [Fintype.card_coe, pow_two, mul_assoc, μ, P, V, pivot, hpivot] using hh

end Hindman168
