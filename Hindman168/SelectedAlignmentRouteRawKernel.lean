import Hindman168.SelectedAlignmentRouteSecured
import Hindman168.FiniteSupportedConditioning

namespace Hindman168
open Filter FiniteMass
open scoped Classical Topology
attribute [local instance] alignmentAddingPairFintype

theorem selected_alignment_earlier_event_outside
    {M : ℕ} (F : MasterParameterFamily) (w : ℕ) (i : Fin M)
    (hZ : 0 < harmonicNormalizer (F.cutoff w i.val) (primorial w))
    (E : (Fin M → ℕ) → Prop)
    (hE : ∀ x y, (∀ j < i, x j = y j) → (E x ↔ E y)) :
    event (selectedAlignmentOutsideRawMass F w i) (fun x => E (insertPivotCoordinate i x 0)) =
      event (globalRawMass (F.cutoff w) (primorial w) M) E := by
  rw [← selected_alignment_raw_pivot_event F w i]
  have he (xp : ({j : Fin M // j ≠ i} → ℕ) × ℤ) :
      E (selectedAlignmentRawPivotInsert i xp) ↔ E (insertPivotCoordinate i xp.1 0) :=
    hE _ _ (selected_alignment_insert_earlier_eq i xp.1 xp.2.toNat 0)
  simp only [he, event_eq_expectation, expectation_conditionalJoint]
  congr 1
  funext x
  by_cases hEx : E (insertPivotCoordinate i x 0) <;>
    simp only [hEx, if_true, if_false, FiniteMass.expectation_const, integerMass_total hZ, one_mul, mul_zero]

theorem selected_alignment_secured_event_original {n M : ℕ} {κ : Type*}
    (f : Fin n ↪o Fin M) (i : Fin n) (F : MasterParameterFamily) (q₀ w : ℕ)
    (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ) (θ : ℝ)
    (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i))
    (E : (Fin M → ℕ) → Prop)
    (hE : ∀ x y, (∀ j < f i, x j = y j) → (E x ↔ E y)) :
    event (conditionalJoint (selectedAlignmentOutsideRawMass F w (f i))
      (fun _ => integerMass (F.cutoff w (f i).val) (primorial w)))
      (fun xp => E (insertPivotCoordinate (f i) xp.1 0) ∧
        selectedAlignmentSignedRouteSecured f i F q₀ w (insertPivotCoordinate (f i) xp.1 0)
          S θ plan b requests xp.2) =
    event (globalRawMass (F.cutoff w) (primorial w) M)
      (fun x => E x ∧ selectedAlignmentSignedRouteSecured f i F q₀ w x S θ plan b requests (x (f i))) := by
  rw [← selected_alignment_raw_pivot_event F w (f i)]
  apply event_congr_on_support
  intro xp hxp
  have hp := (selected_alignment_raw_pivot_support F w (f i) xp hxp).1
  have hz : (xp.2.toNat : ℤ) = xp.2 := Int.toNat_of_nonneg hp
  apply and_congr
  · exact hE _ _ (selected_alignment_insert_earlier_eq (f i) xp.1 0 xp.2.toNat)
  · rw [← hz]
    exact selected_alignment_outside_secured_natural f i F q₀ w xp.1 xp.2.toNat S θ plan b requests

end Hindman168
