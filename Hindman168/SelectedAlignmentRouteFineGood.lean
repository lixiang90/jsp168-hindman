import Hindman168.SelectedAlignmentRouteSecured
import Hindman168.SelectedAlignmentCompleteCell
import Hindman168.SelectedAlignmentNativeRouteFailure
import Hindman168.PositivePrincipalSumConditioningMaster

/-! The actual local cover is a function of the outside sample and the
original microcell/residue exposure. Its exceptional mass is controlled
under the exact original signed conditional joint law. -/
namespace Hindman168
open Filter FiniteMass
open scoped Classical Topology ENNReal NNReal BigOperators
attribute [local instance] alignmentAddingPairFintype

noncomputable def selectedAlignmentFineRouteGood {n M : ℕ} {κ : Type*}
    (F : MasterParameterFamily) (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (i : Fin n) (q₀ w : ℕ) (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ) (θ : ℝ)
    (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i))
    (outside : {j : Fin M // j ≠ principalAlignmentEmbedding e heM i} → ℕ)
    (t : ℤ × ℤ) : Prop :=
  ∀ p : ℕ, principalMicrocellExposure (selectedPrincipalMicrocellWidth F e w i)
    (F.modulus w) p = t →
    selectedAlignmentCompleteCell F e w i p ∧
    ((3 / (4 * ((principalPivotRoutes plan).card : ℝ≥0)) : ℝ≥0) : ℝ≥0∞) ≤
      selectedAlignmentRawRouteCellMass F e heM i q₀ w
        (insertPivotCoordinate (principalAlignmentEmbedding e heM i) outside p) S θ plan b requests

theorem selected_alignment_fine_route_good_iff {n M : ℕ} {κ : Type*}
    (F : MasterParameterFamily) (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (i : Fin n) (q₀ w : ℕ) (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ) (θ : ℝ)
    (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i))
    (outside : {j : Fin M // j ≠ principalAlignmentEmbedding e heM i} → ℕ) (p : ℕ) :
    selectedAlignmentFineRouteGood F e heM i q₀ w S θ plan b requests outside
      (principalMicrocellExposure (selectedPrincipalMicrocellWidth F e w i) (F.modulus w) p) ↔
    selectedAlignmentCompleteCell F e w i p ∧
    ((3 / (4 * ((principalPivotRoutes plan).card : ℝ≥0)) : ℝ≥0) : ℝ≥0∞) ≤
      selectedAlignmentRawRouteCellMass F e heM i q₀ w
        (insertPivotCoordinate (principalAlignmentEmbedding e heM i) outside p) S θ plan b requests := by
  constructor
  · intro h
    exact h p rfl
  · rintro ⟨hc,hm⟩ q hq
    refine ⟨(selected_alignment_complete_cell_exposure_eq F e w i q p hq).mpr hc, ?_⟩
    have he := selected_alignment_raw_route_cell_mass_invariant F e heM i q₀ w
      (insertPivotCoordinate (principalAlignmentEmbedding e heM i) outside q)
      (insertPivotCoordinate (principalAlignmentEmbedding e heM i) outside p)
      (selected_alignment_insert_earlier_eq _ outside q p)
      (by simpa only [insertPivotCoordinate_self] using hq) S θ plan b requests
    rw [he]
    exact hm

theorem selected_alignment_fine_route_failure_tendsto
    {d n M : ℕ} {κ : Type*} {A : Finset ℚ} {Poly : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A Poly F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n) (q₀ : ℕ)
    (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ) (θ : ℝ)
    (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i))
    (hlocal : Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) M)
      (fun x => selectedAlignmentRawRouteCellMass F e heM i q₀ w x S θ plan b requests <
        ((3 / (4 * ((principalPivotRoutes plan).card : ℝ≥0)) : ℝ≥0) : ℝ≥0∞))) atTop (𝓝 0)) :
    Tendsto (fun w => event
      (conditionalJoint (selectedAlignmentOutsideRawMass F w (principalAlignmentEmbedding e heM i))
        (fun _ => integerMass (F.cutoff w (energyPrincipal e i)) (primorial w)))
      (fun xp => ¬ selectedAlignmentFineRouteGood F e heM i q₀ w S θ plan b requests xp.1
        (principalMicrocellExposure (selectedPrincipalMicrocellWidth F e w i) (F.modulus w) xp.2)))
      atTop (𝓝 0) := by
  let pivot := principalAlignmentEmbedding e heM i
  let μ := fun w => selectedAlignmentOutsideRawMass F w pivot
  let ν := fun w => integerMass (F.cutoff w (energyPrincipal e i)) (primorial w)
  let badCell := fun (w : ℕ) (x : Fin M → ℕ) => ¬ selectedAlignmentCompleteCell F e w i (x pivot)
  let badCover := fun (w : ℕ) (x : Fin M → ℕ) => selectedAlignmentRawRouteCellMass F e heM i q₀ w x S θ plan b requests <
    ((3 / (4 * ((principalPivotRoutes plan).card : ℝ≥0)) : ℝ≥0) : ℝ≥0∞)
  have hcell : Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) M) (badCell w)) atTop (𝓝 0) := by
    apply (selected_alignment_complete_cell_failure_tendsto hF e heM i).congr'
    filter_upwards [selected_alignment_raw_coordinate_event hF pivot] with w hw
    exact (hw (fun p => ¬ selectedAlignmentCompleteCell F e w i p)).symm
  have heq (w : ℕ) : event (conditionalJoint (μ w) (fun _ => ν w))
      (fun xp => ¬ selectedAlignmentFineRouteGood F e heM i q₀ w S θ plan b requests xp.1
        (principalMicrocellExposure (selectedPrincipalMicrocellWidth F e w i) (F.modulus w) xp.2)) =
      event (globalRawMass (F.cutoff w) (primorial w) M) (fun x => badCell w x ∨ badCover w x) := by
    rw [← selected_alignment_raw_pivot_event F w pivot]
    apply event_congr_on_support
    intro xp hxp
    have hp := (selected_alignment_raw_pivot_support F w pivot xp hxp).1
    have hz : (xp.2.toNat : ℤ) = xp.2 := Int.toNat_of_nonneg hp
    rw [← hz, selected_alignment_fine_route_good_iff]
    simp only [selectedAlignmentRawPivotInsert, insertPivotCoordinate_self,
      badCell, badCover, not_and_or, not_le]
    rfl
  have hor : Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) M)
      (fun x => badCell w x ∨ badCover w x)) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (show Tendsto (fun w =>
        event (globalRawMass (F.cutoff w) (primorial w) M) (badCell w) +
        event (globalRawMass (F.cutoff w) (primorial w) M) (badCover w)) atTop (𝓝 0) from
          by simpa only [add_zero] using hcell.add hlocal)
    · filter_upwards [alignmentGlobalRawMass_geometry hF] with w hw
      exact event_nonneg _ _ hw.1
    · filter_upwards [alignmentGlobalRawMass_geometry hF] with w hw
      exact event_or_le_add _ _ _ hw.1
  apply hor.congr'
  exact Eventually.of_forall (fun w => (heq w).symm)

end Hindman168
